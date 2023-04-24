"""
Implementation of the Hindley-Milner Unification Algorithm
"""

from solvent.syn import Type, TypeVar, RType

def base_type_eq(t1: Type, t2: Type) -> bool:
    """
    We can probably override __eq__ at some point. I'm lazy right now.
    This function implements equality between types
    """

    match (t1, t2):
        case (TypeVar(name=n1), TypeVar(name=n2)):
            return n1 == n2
        case (RType(base=v1, predicate=_), RType(base=v2, predicate=_)):
            return v1 == v2
        case (ArrowType(args=args1, ret=ret1), ArrowType(args=args2, ret=ret2)):
            args_eq = all(map(lambda a: base_type_eq(a[0], a[1]), zip(args1, args2)))
            return args_eq and base_type_eq(ret1, ret2)
        case _: 
            return False


def unify(constrs, show_work=False):
    if len(constrs) == 0:
        return []
    else:
        top = constrs[0]
        rest = constrs[1:]

        if show_work:
            print("====== unify ======")
            print(f"=> {top}")
            for c in rest:
                print(c)

        # ignore subtype constraints
        if isinstance(top, SubType):
            return unify(rest, show_work)

        lX = tvar_name(top.lhs)
        rX = tvar_name(top.rhs)

        if base_type_eq(top.lhs, top.rhs):
            return unify(rest, show_work)
        # if lhs is variable
        elif lX is not None and lX not in free_vars(top.rhs):
            return unify(subst(lX, top.rhs, rest), show_work) + [(lX, top.rhs)]
        # if rhs is variable
        elif rX is not None and rX not in free_vars(top.lhs):
            return unify(subst(rX, top.lhs, rest), show_work) + [(rX, top.lhs)]
        # if both are functions variables
        elif (isinstance(top.lhs, ArrowType)
            and isinstance(top.rhs, ArrowType)
            and len(top.lhs.args) == len(top.rhs.args)):
            arg_constrs = list(map(
                lambda a: BaseEq(lhs=a[0], rhs=a[1]),
                zip(top.lhs.args, top.rhs.args)
            ))
            ret_constr = BaseEq(lhs=top.lhs.ret, rhs=top.rhs.ret)
            return unify(arg_constrs + [ret_constr] + rest, show_work)
        else:
            raise Exception(f"{top.lhs} is incompatible with {top.rhs}")


def tvar_name(typ: Type):
    """ 
    Returns the type variable name of `typ' if it exists, and none otherwise.
    """

    match typ:
        case RType(base=TypeVar(name=name)):
            return name


def free_vars(typ: Type):
    """
    Returns the free variables of typ.
    """

    match typ:
        case RType(base=TypeVar(name=n)):
            return [n]
        case RType():
            return []
        case ArrowType(args=args, ret=ret):
            return sum([free_vars(a) for a in args], []) + free_vars(ret)
        case x:
            print(x)
            raise NotImplementedError


def subst(name: str, typ: Type, constrs: List[BaseEq]) -> List[BaseEq]:
    res = []
    for x in constrs:
        match x:
            case BaseEq(lhs=lhs, rhs=rhs):
                res.append(BaseEq(
                    lhs=subst_one(name, typ, lhs),
                    rhs=subst_one(name, typ, rhs)
                ))
            case SubType(assumes=asms, lhs=lhs, rhs=rhs):
                res.append(SubType(
                    assumes=asms,
                    lhs=subst_one(name, typ, lhs),
                    rhs=subst_one(name, typ, rhs)
                ))
                
    return res


def subst_one(name: str, tar: Type, src: Type) -> Type:
    match src:
        case RType(base=TypeVar(name=n)) if name == n:
            return tar
        case RType():
            return src
        case ArrowType(args=args, ret=ret):
            return ArrowType(
                args=[subst_one(name, tar, x) for x in args],
                ret=subst_one(name, tar, ret)
            )
        case x:
            print("subst_one:", x)
            raise NotImplementedError


def apply(typ: Type, solution) -> Type:
    """
    Given a type, resolve all type variables using `solution'.
    """

    match typ:
        case RType(base=v, predicate=p):
            changed = False
            if isinstance(v, TypeVar):
                base_ty = solution[v.name].base
                changed = True
            else:
                base_ty = v

            if isinstance(p, PredicateVar) and p.name in solution:
                changed = True
                p = solution[p.name]

            if changed:
                return apply(RType(base_ty, p), solution)
            else:
                return RType(base_ty, p)
        case ArrowType(args=args, ret=ret):
            return ArrowType(
                args=[apply(t, solution) for t in args],
                ret=apply(ret, solution)
            )
        case x:
            return typ
