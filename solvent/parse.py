import ast
from logging import debug, info
from typing import Annotated, Any, Dict, List, get_args, get_origin

import solvent
from solvent import syntax as syn
from solvent.qualifiers import Qualifier


def string_to_expr(string: str) -> syn.Expr:
    pyast = ast.parse(string)
    if isinstance(pyast.body[0], ast.Expr):
        return Parser({}).parse_expr(pyast.body[0].value)
    else:
        raise Exception(f"Can't parse `{string}`")


class Parser:
    def __init__(self, typing_hints: Dict[str, Any], strict=True):
        self.typing_hints = typing_hints
        self.strict = strict

        # a map from the alias names of imports to
        # their resolved "cannonical" names
        self.modules: Dict[str, str] = {}

    def parse(self, tree: ast.AST) -> List[syn.Stmt]:
        """
        Parse a python AST into our internal AST representation.
        * `strict`: (default=True)
          When `True`, only parse supported expressions. Disabling this option
          allows us to parse whole files, ignoring unsupported things. This
          is meant to be temporary and exists so that we don't have to support
          everything up front.
        """

        match tree:
            case ast.Module(body=body):
                return sum([self.parse(b) for b in body], [])
            case ast.Import(names=names):
                for n in names:
                    if n.asname is None:
                        used_name = n.name
                    else:
                        used_name = n.asname
                    self.modules[used_name] = n.name

                return []
            case ast.ImportFrom(module=module, names=names):
                for n in names:
                    if n.asname is None:
                        used_name = n.name
                    else:
                        used_name = n.asname
                    self.modules[f"{used_name}"] = f"{module}.{n.name}"

                return []
            case ast.FunctionDef(name=name, args=args, body=body, returns=returns):
                if "return" in self.typing_hints:
                    ret_ann = self.parse_hint(self.typing_hints["return"])
                    if returns is not None:
                        ret_ann = ret_ann.ast(returns)
                elif returns is not None:
                    ret_ann = self.parse_annotation(returns).ast(returns)
                else:
                    ret_ann = None

                return [
                    syn.FunctionDef(
                        name=name,
                        args=[self.parse_argument(a) for a in args.args],
                        body=sum([self.parse(b) for b in body], []),
                        return_annotation=ret_ann,
                    ).ast(tree)
                ]
            case ast.If(test=test, body=body, orelse=orelse):
                return [
                    syn.If(
                        test=self.parse_expr(test),
                        body=sum([self.parse(b) for b in body], []),
                        orelse=sum([self.parse(b) for b in orelse], []),
                    ).ast(tree)
                ]
            case ast.Assign(targets=[ast.Name(id=id)], value=e):
                return [syn.Assign(id, self.parse_expr(e)).ast(tree)]
            case ast.Return(value=value):
                return [syn.Return(value=self.parse_expr(value)).ast(tree)]
            case ast.Expr(value=value) if not self.strict:
                return [syn.Assign("_", self.parse_expr(value)).ast(tree)]
            case ast.Pass():
                return []
            case _ if not self.strict:
                info(ast.dump(tree, indent=2))
                return []
            case _:
                raise NotImplementedError(ast.dump(tree, indent=2))

    def parse_argument(self, arg: ast.arg) -> syn.Argument:
        if arg.arg in self.typing_hints:
            ann = self.parse_hint(self.typing_hints[arg.arg]).ast(arg)
        elif isinstance(arg.annotation, ast.Subscript):
            ann = self.parse_annotation(arg.annotation)
        else:
            ann = None

        return syn.Argument(name=arg.arg, annotation=ann)

    def parse_hint(self, hint: type) -> syn.Type:
        if get_origin(hint) is Annotated:
            args = get_args(hint)
            base = args[0]
            rest = list(args[1:])[0]

            base_rtype = self.parse_base(base)
            match rest:
                case Qualifier():
                    return base_rtype.set_predicate(syn.Conjoin([rest.template]))
                case bool():
                    return base_rtype.set_predicate(
                        syn.Conjoin([syn.BoolLiteral(rest)])
                    )
                case x:
                    raise NotImplementedError(x)
        else:
            return self.parse_base(hint)

    def parse_base(self, hint: type) -> syn.Type:
        if hint == int:
            return syn.RType.lift(syn.Int())
        elif hint == bool:
            return syn.RType.lift(syn.Bool())
        else:
            raise NotImplementedError(hint)

    def parse_annotation(self, ann) -> syn.Type:
        match ann:
            case ast.Name(id="int"):
                return syn.RType.lift(syn.Int())
            case ast.Name(id="bool"):
                return syn.RType.lift(syn.Bool())
            case ast.Constant(value=v):
                return self.parse_refinement(v)
            case ast.Set(elts=[ast.BinOp(left=base, op=ast.BitOr(), right=refinement)]):
                base_type = self.parse_annotation(base)
                if isinstance(base_type, syn.RType):
                    base_type.predicate = syn.Conjoin([self.parse_expr(refinement)])
                return base_type
            case ast.Subscript(
                value=ast.Name(id=id), slice=ast.Tuple(elts=[base_ty, predicate])
            ) if id in self.modules and self.modules[id] == "solvent.Refine":
                rtype = self.parse_annotation(base_ty)
                # OK are you ready
                # We are doing some crazy magic so that we can write out
                # refinement types in base python without having to do things
                # like parsing comments etc.
                #
                # For example, we can write `Refine[int, Q[0] <= V]` which is the
                # type of ints that are greater than or equal to 0. We implement this
                # by having Q be a magic object that has subscript and <= overridden
                # so that they create a Qualifier object.
                #
                # When we are parsing this from an annotation, we have access to the
                # function object and we can get at this Qualifier object directly.
                # However, when are are parsing the whole file, we haven't executed
                # any python yet. And so we just have the syntax objects. The following
                # code wraps the Qualifier syntax like so:
                # ```
                # pred = <qualifier ast>
                # ```
                # Then compiles and executes it. At the moment, I am hardcoding
                # the names `Q`, `V`, and `_`. I will later make this more robust.
                locals = {}
                exec(
                    compile(
                        ast.fix_missing_locations(
                            ast.Interactive(
                                [
                                    ast.Assign(
                                        targets=[ast.Name(id="pred", ctx=ast.Store())],
                                        value=predicate,
                                    )
                                ]
                            )
                        ),
                        "play.py",
                        "single",
                    ),
                    {"Q": solvent.Q, "V": solvent.V, "_": solvent._},
                    locals,
                )

                match locals["pred"]:
                    case Qualifier():
                        return rtype.set_predicate(
                            syn.Conjoin([locals["pred"].template])
                        )
                    case bool():
                        return rtype.set_predicate(
                            syn.Conjoin([syn.BoolLiteral(locals["pred"])])
                        )
                    case x:
                        raise NotImplementedError(x)
            case ast.Subscript(
                value=ast.Name(id="Callable"),
                slice=ast.Tuple(elts=[*arg_types, ret_type]),
            ):
                if ret_type is not None:
                    ret = self.parse_annotation(ret_type)
                else:
                    ret = syn.RType.lift(syn.Unit())

                return syn.ArrowType(
                    type_abs={},
                    args=[
                        (syn.NameGenerator.fresh("x"), self.parse_annotation(a))
                        for a in arg_types
                    ],
                    ret=ret,
                )
            case x:
                if x is not None and isinstance(x, ast.AST):
                    info(ast.dump(ann, indent=2))
                raise NotImplementedError(x)

    def parse_expr(self, expr) -> syn.Expr:
        match expr:
            case ast.Compare(left=left, ops=ops, comparators=comps):
                if len(ops) > 1 or len(comps) > 1:
                    raise NotImplementedError

                op = ops[0]
                right = comps[0]
                return syn.BoolOp(
                    lhs=self.parse_expr(left),
                    op=self.binop_str(op),
                    rhs=self.parse_expr(right),
                ).ast(expr)
            case ast.Name(id=name) if name == "V":
                return syn.V().ast(expr)
            case ast.Name(id=name):
                return syn.Variable(name=name).ast(expr)
            case ast.BinOp(left=left, op=op, right=right):
                return syn.ArithBinOp(
                    lhs=self.parse_expr(left),
                    op=self.binop_str(op),
                    rhs=self.parse_expr(right),
                ).ast(expr)
            case ast.BoolOp(op=ast.And(), values=[lhs, rhs]):
                return syn.BoolOp(
                    lhs=self.parse_expr(lhs), op="and", rhs=self.parse_expr(rhs)
                ).ast(expr)
            case ast.Constant(value=val):
                if type(val) == int:
                    return syn.IntLiteral(value=val).ast(expr)
                elif type(val) == bool:
                    return syn.BoolLiteral(value=val).ast(expr)
                elif type(val) == str:
                    return syn.StrLiteral(value=val).ast(expr)
                else:
                    raise NotImplementedError(val, type(val))
            case ast.List(elts=elts, ctx=ast.Load()):
                exprs = [self.parse_expr(e) for e in elts]
                return syn.ListLiteral(exprs).ast(expr)
            case ast.Call(func=func, args=args):
                return syn.Call(
                    function_name=self.parse_expr(func),
                    arglist=[self.parse_expr(e) for e in args],
                ).ast(expr)
            case ast.UnaryOp(op=ast.USub(), operand=val):
                return syn.Neg(self.parse_expr(val)).ast(expr)
            case ast.Subscript(value=lst, slice=slice_expr):
                return syn.Subscript(
                    self.parse_expr(lst), self.parse_expr(slice_expr)
                ).ast(expr)
            case ast.Dict():
                return syn.DictLit().ast(expr)
            case ast.Attribute(value=value, attr=attr, ctx=ast.Load()):
                return syn.GetAttr(self.parse_expr(value), attr).ast(expr)
            case x:
                if x is not None:
                    raise NotImplementedError(ast.dump(expr, indent=2))
                else:
                    raise NotImplementedError(x)

    def parse_refinement(self, input: str) -> syn.RType:
        stripped = input[1:-1]
        typ, refinement = stripped.split("|")
        refine_expr = string_to_expr(refinement)
        match typ.strip():
            case "int":
                return syn.RType(syn.Int(), syn.Conjoin([refine_expr]))
            case "bool":
                return syn.RType(syn.Bool(), syn.Conjoin([refine_expr]))
            case _:
                raise NotImplementedError

    def binop_str(self, op):
        match op:
            case ast.Eq():
                return "=="
            case ast.NotEq():
                return "!="
            case ast.Lt():
                return "<"
            case ast.LtE():
                return "<="
            case ast.Gt():
                return ">"
            case ast.GtE():
                return ">="
            case ast.Add():
                return "+"
            case ast.Sub():
                return "-"
            case ast.Mult():
                return "*"
            case ast.Div():
                return "/"
            case x:
                return f"`{x}`"
