"""
Implement Liquid Type inference
"""

from solvent import check, subtype, parse, liquid, pretty_print as pp, syn

from functools import reduce


def solve(constrs, solution):

    refinement_vars = set()

    print("SubTyping constraints")
    for c in constrs:
        if isinstance(c, check.SubType):
            print(pp.pstring_cvar(c))
            if isinstance(c.lhs.predicate, syn.TypeVar):
                refinement_vars.add(c.lhs.predicate.name)
            if isinstance(c.rhs.predicate, syn.TypeVar):
                refinement_vars.add(c.rhs.predicate.name)

    # add qualifiers to the solution
    # TODO: generate this automatically
    #  * < 
    for rv in refinement_vars:
        solution[rv] = list(map(parse.string_to_expr, [
            "(0 < V)",
            "(0 <= V)",
            "(x <= V)",
            "(y <= V)",
            "(V > x)",
            "(V > y)",
        ]))

    print("======")
    return liquid.constraints_valid(constrs, solution)


def constraints_valid(constrs, solution):
    """
    Check if solution satisfies every constraint in constrs.
    Returns the first constraints that is not satisified.
    Returns None otherwise.
    """

    for c in constrs:
        if isinstance(c, check.SubType):
            lhs = check.finish(c.lhs, solution)
            rhs = check.finish(c.rhs, solution)
            if not subtype.subtype(c.assumes, lhs, rhs):
                print(f"NBT: {pp.pstring_type(lhs)} ! <: {pp.pstring_type(rhs)}")
                return constraints_valid(constrs, weaken(c, solution))
            print(f"NBT: {pp.pstring_type(lhs)} <: {pp.pstring_type(rhs)}")

    return solution


def weaken(c, solution):
    """
    Weaken constr and return a new solution.

    Only implementing case 2 right now. I never generate constraints
    of the other forms. I probably should.
    """

    print(f"Weakening {pp.pstring_cvar(c)}")

    if not isinstance(c.rhs.predicate, syn.TypeVar):
        raise NotImplementedError("Can only weaken lists of constraints.")

    name = c.rhs.predicate.name

    qs = []
    for q in solution[name]:

        assumes = c.assumes
        lhs = c.lhs
        if isinstance(c.lhs.predicate, syn.TypeVar):
            assumes += solution[c.lhs.predicate.name]
            lhs = syn.RType.base(c.lhs.value)  # kind of a hack

        if subtype.subtype(assumes, lhs, syn.RType(c.rhs.value, q)):
            qs += [q]

    solution[name] = qs
    return solution
