import ast
from typing import Annotated, Any, Dict, List, get_args, get_origin

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
            case ast.Import(names=names) if not self.strict:
                for n in names:
                    print(n.name, n.asname)
                return []
            case ast.ImportFrom() if not self.strict:
                return []
            case ast.FunctionDef(name=name, args=args, body=body, returns=returns):
                if returns is not None and "return" in self.typing_hints:
                    ret_ann = self.parse_hint(self.typing_hints["return"]).ast(returns)
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
            case _:
                print(ast.dump(tree, indent=2))
                raise NotImplementedError

    # def parse(tree: ast.AST, typing_hints: Dict[str, Any], strict=True) ->
    # List[syn.Stmt]:
    #     match tree:
    #         case ast.Module(body=body):
    #             return sum([parse(b, typing_hints) for b in body], [])
    #         case ast.Import() if not strict:
    #             return []
    #         case ast.FunctionDef(name=name, args=args, body=body, returns=returns):
    #             if returns is not None and "return" in typing_hints:
    #                 ret_ann = parse_hint(typing_hints["return"]).ast(returns)
    #             else:
    #                 ret_ann = None

    #             return [
    #                 syn.FunctionDef(
    #                     name=name,
    #                     args=[parse_argument(a, typing_hints) for a in args.args],
    #                     body=sum([parse(b, typing_hints) for b in body], []),
    #                     return_annotation=ret_ann,
    #                 ).ast(tree)
    #             ]
    #         case ast.If(test=test, body=body, orelse=orelse):
    #             return [
    #                 syn.If(
    #                     test=parse_expr(test),
    #                     body=sum([parse(b, typing_hints) for b in body], []),
    #                     orelse=sum([parse(b, typing_hints) for b in orelse], []),
    #                 ).ast(tree)
    #             ]
    #         case ast.Assign(targets=[ast.Name(id=id)], value=e):
    #             return [syn.Assign(id, parse_expr(e)).ast(tree)]
    #         case ast.Return(value=value):
    #             return [syn.Return(value=parse_expr(value)).ast(tree)]
    #         case _:
    #             print(ast.dump(tree, indent=2))
    #             raise NotImplementedError

    def parse_argument(self, arg: ast.arg) -> syn.Argument:
        print(arg.annotation)
        if arg.arg in self.typing_hints:
            ann = self.parse_hint(self.typing_hints[arg.arg]).ast(arg)
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
            case ast.Subscript(value=ast.Name(id="Refine")):
                raise NotImplementedError(ast.dump(ann, indent=2))
            case ast.Subscript(
                value=ast.Name(id="Callable"),
                slice=ast.Tuple(elts=[*arg_types, ret_type]),
            ):
                if ret_type is not None:
                    ret = self.parse_annotation(ret_type)
                else:
                    ret = syn.RType.lift(syn.Unit())

                return syn.ArrowType(
                    args=[
                        (syn.NameGenerator.fresh("x"), self.parse_annotation(a))
                        for a in arg_types
                    ],
                    ret=ret,
                )
            case x:
                if x is not None and isinstance(x, ast.AST):
                    print(ast.dump(ann, indent=2))
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
                else:
                    raise NotImplementedError
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
                    print(ast.dump(expr, indent=2))
                raise NotImplementedError

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
