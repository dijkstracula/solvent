import ast
from solvent import syn
from typing import Union, Optional
import re


def parse(tree: ast.AST) -> syn.Stmt:
    match tree:
        case ast.Module(body=body):
            return parse(body[0])
        case ast.FunctionDef(name=name, args=args, body=body, returns=returns):
            return syn.FunctionDef(
                name=name,
                args=[parse_argument(a) for a in args.args],
                body=[parse(b) for b in body],
                return_annotation=parse_annotation(returns)
            )
        case ast.If(test=test, body=body, orelse=orelse):
            return syn.If(
                test=parse_expr(test),
                body=[parse(b) for b in body],
                orelse=[parse(b) for b in orelse],
            )
        case ast.Return(value=value):
            return syn.Return(value=parse_expr(value))
        case _:
            print(ast.dump(tree, indent=2))
            raise NotImplementedError


def parse_argument(arg: ast.arg) -> syn.Argument:
    return syn.Argument(
        name=arg.arg,
        annotation=parse_annotation(arg.annotation)
    )


def parse_annotation(ann: Union[ast.Str, ast.Name]) -> Optional[syn.RType]:
    if ann is not None:
        match ann:
            case ast.Name(id="int"):
                return syn.RType.base(syn.Int())
            case ast.Name(id="bool"):
                return syn.RType.base(syn.Bool())
            case ast.Constant(value=v):
                return parse_refinement(v)
            case ast.Set(
                    elts=[ast.Compare(
                        left=ast.BinOp(
                            left=base,
                            op=ast.BitOr(),
                            right=rhs),
                        ops=[op],
                        comparators=[val])]):
                base_type = parse_annotation(base)
                base_type.predicate = syn.BoolOp(
                        lhs=parse_expr(rhs),
                        op=binop_str(op),
                        rhs=parse_expr(val)
                    )
                return base_type
            case _:
                print(ast.dump(ann, indent=2))
                raise NotImplementedError

    return None


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
        case ast.Name(id=name):
            return syn.Variable(name=name)
        case ast.BinOp(left=left, op=op, right=right):
            return syn.ArithBinOp(
                lhs=parse_expr(left),
                op=binop_str(op),
                rhs=parse_expr(right),
            )
        case ast.Constant(value=val):
            if type(val) == int:
                return syn.IntLiteral(value=val)
            elif type(val) == bool:
                return syn.BoolLiteral(value=val)
            else:
                raise NotImplementedError
        case _:
            print(ast.dump(expr, indent=2))
            raise NotImplementedError


def parse_refinement(input: str) -> syn.RType:
    stripped = input[1:-1]
    typ, refinement = stripped.split("|")
    # parse the refinement as a python ast
    pyast = ast.parse(refinement.strip())
    refine_expr = parse_expr(pyast.body[0].value)
    match typ.strip():
        case "int":
            return syn.RType(syn.Int(), refine_expr)
        case "bool":
            return syn.RType(syn.Bool(), refine_expr)
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
