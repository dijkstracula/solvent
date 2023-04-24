import ast
from solvent import syn
from typing import List


def string_to_expr(string: str) -> syn.Expr:
    pyast = ast.parse(string)
    if isinstance(pyast.body[0], ast.Expr):
        return parse_expr(pyast.body[0].value)
    else:
        raise Exception(f"Can't parse `{string}`")


def parse(tree: ast.AST) -> List[syn.Stmt]:
    match tree:
        case ast.Module(body=body):
            return sum([parse(b) for b in body], [])
        case ast.FunctionDef(name=name, args=args, body=body, returns=returns):
            if returns is not None:
                ret_ann = parse_annotation(returns)
            else:
                ret_ann = syn.RType.lift(syn.Unit())

            return [syn.FunctionDef(
                name=name,
                args=[parse_argument(a) for a in args.args],
                body=sum([parse(b) for b in body], []),
                return_annotation=ret_ann
            )]
        case ast.If(test=test, body=body, orelse=orelse):
            return [syn.If(
                test=parse_expr(test),
                body=sum([parse(b) for b in body], []),
                orelse=sum([parse(b) for b in orelse], []),
            )]
        case ast.Return(value=value):
            return [syn.Return(value=parse_expr(value))]
        case _:
            print(ast.dump(tree, indent=2))
            raise NotImplementedError


def parse_argument(arg: ast.arg) -> syn.Argument:
    if arg.annotation is None:
        ann = None
    else:
        ann = parse_annotation(arg.annotation)
    return syn.Argument(
        name=arg.arg,
        annotation=ann
    )


def parse_annotation(ann) -> syn.Type:
    match ann:
        case ast.Name(id="int"):
            return syn.RType.lift(syn.Int())
        case ast.Name(id="bool"):
            return syn.RType.lift(syn.Bool())
        case ast.Constant(value=v):
            return parse_refinement(v)
        case ast.Set(
                elts=[
                    ast.BinOp(
                        left=base,
                        op=ast.BitOr(),
                        right=refinement)]):
            base_type = parse_annotation(base)
            if isinstance(base_type, syn.RType):
                base_type.predicate = syn.Conjoin([parse_expr(refinement)])
            return base_type
        case ast.Subscript(
                value=ast.Name(id='Callable'),
                slice=ast.Tuple(elts=[*arg_types, ret_type])
        ):
            if ret_type is not None:
                ret = parse_annotation(ret_type)
            else:
                ret = syn.RType.lift(syn.Unit())

            return syn.ArrowType(
                args=[parse_annotation(a) for a in arg_types],
                ret=ret
            )
        case x:
            if x is not None:
                print(ast.dump(ann, indent=2))
            raise NotImplementedError


def parse_expr(expr) -> syn.Expr:
    match expr:
        case ast.Compare(left=left, ops=ops, comparators=comps):
            if len(ops) > 1 or len(comps) > 1:
                raise NotImplementedError

            op = ops[0]
            right = comps[0]
            return syn.BoolOp(
                lhs=parse_expr(left),
                op=binop_str(op),
                rhs=parse_expr(right),
            )
        case ast.Name(id=name) if name == "V":
            return syn.V()
        case ast.Name(id=name):
            return syn.Variable(name=name)
        case ast.BinOp(left=left, op=op, right=right):
            return syn.ArithBinOp(
                lhs=parse_expr(left),
                op=binop_str(op),
                rhs=parse_expr(right),
            )
        case ast.BoolOp(op=ast.And(), values=[lhs, rhs]):
            return syn.BoolOp(
                lhs=parse_expr(lhs),
                op="and",
                rhs=parse_expr(rhs)
            )
        case ast.Constant(value=val):
            if type(val) == int:
                return syn.IntLiteral(value=val)
            elif type(val) == bool:
                return syn.BoolLiteral(value=val)
            else:
                raise NotImplementedError
        case ast.Call(func=func, args=args):
            return syn.Call(
                function_name=parse_expr(func),
                arglist=[parse_expr(e) for e in args]
            )
        case x:
            if x is not None:
                print(ast.dump(expr, indent=2))
            raise NotImplementedError


def parse_refinement(input: str) -> syn.RType:
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


def binop_str(op):
    match op:
        case ast.Eq(): return "=="
        case ast.NotEq(): return "!="
        case ast.Lt(): return "<"
        case ast.LtE(): return "<="
        case ast.Gt(): return ">"
        case ast.GtE(): return ">="
        case ast.Add(): return "+"
        case ast.Sub(): return "-"
        case ast.Mult(): return "*"
        case ast.Div(): return "/"
        case x: return f"`{x}`"
