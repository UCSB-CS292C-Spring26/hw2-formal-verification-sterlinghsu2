"""
CS292C Homework 2 — Problem 1: Z3 Warm-Up + EUF Puzzle (15 points)
===================================================================
Complete each function below. Run this file to check your answers.
"""

from z3 import *


# ---------------------------------------------------------------------------
# Part (a) — 3 pts
# Find integers x, y, z such that x + 2y = z, z > 10, x > 0, y > 0.
# ---------------------------------------------------------------------------
def part_a():
    x, y, z = Ints('x y z')
    s = Solver()

    s.add(x + 2 * y == z)
    s.add(z > 10)
    s.add(x > 0)
    s.add(y > 0)

    print("=== Part (a) ===")
    if s.check() == sat:
        m = s.model()
        print(f"SAT: x={m[x]}, y={m[y]}, z={m[z]}")
    else:
        print("UNSAT (unexpected!)")
    print()


# ---------------------------------------------------------------------------
# Part (b) — 3 pts
# Prove validity of: ∀x. x > 5 → x > 3
# Hint: A formula F is valid iff ¬F is unsatisfiable.
# ---------------------------------------------------------------------------
def part_b():
    x = Int('x')
    s = Solver()

    # Negate the formula: ¬(x > 5 → x > 3) ≡ (x > 5 ∧ ¬(x > 3))
    s.add(Not(Implies(x > 5, x > 3)))

    print("=== Part (b) ===")
    result = s.check()
    if result == unsat:
        print("Valid! (negation is UNSAT)")
    else:
        print(f"Not valid — counterexample: {s.model()}")
    print()


# ---------------------------------------------------------------------------
# Part (c) — 5 pts: The EUF Puzzle
#
# Formula:  f(f(x)) = x  ∧  f(f(f(x))) = x  ∧  f(x) ≠ x
#
# STEP 1: Check satisfiability with Z3. (2 pts)
#
# STEP 2: Use Z3 to derive WHY the result holds. (3 pts)
#   Write a series of Z3 validity checks that demonstrate the key reasoning
#   steps. For example, from f(f(x)) = x, what can you derive about f(f(f(x)))?
#   Each check should print what it's testing and whether it holds.
#   Hint: Apply f to both sides of the first equation.
# ---------------------------------------------------------------------------
def part_c():
    S = DeclareSort('S')
    x = Const('x', S)
    f = Function('f', S, S)
    s = Solver()

    s.add(f(f(x)) == x)
    s.add(f(f(f(x))) == x)
    s.add(f(x) != x)

    print("=== Part (c) ===")
    result = s.check()
    if result == sat:
        print(f"SAT: {s.model()}")
    else:
        print("UNSAT")

    # --- Derivation: WHY is it UNSAT? ---

    # Step 1: From f(f(x)) = x, applying f to both sides gives f(f(f(x))) = f(x).
    # This is valid because f is a function — equal inputs produce equal outputs.
    s1 = Solver()
    step1 = Implies(f(f(x)) == x, f(f(f(x))) == f(x))
    s1.add(Not(step1))
    r1 = s1.check()
    print(f"Step 1: f(f(x))=x  =>  f(f(f(x)))=f(x)  :  {'Valid' if r1 == unsat else 'INVALID'}")

    # Step 2: Combining f(f(f(x))) = f(x) (from step 1) with f(f(f(x))) = x gives f(x) = x.
    s2 = Solver()
    step2 = Implies(And(f(f(f(x))) == f(x), f(f(f(x))) == x), f(x) == x)
    s2.add(Not(step2))
    r2 = s2.check()
    print(f"Step 2: f(f(f(x)))=f(x) AND f(f(f(x)))=x  =>  f(x)=x  :  {'Valid' if r2 == unsat else 'INVALID'}")

    # Step 3: f(x) = x contradicts f(x) ≠ x, so the full conjunction is UNSAT.
    s3 = Solver()
    step3 = And(f(x) == x, f(x) != x)
    s3.add(step3)
    r3 = s3.check()
    print(f"Step 3: f(x)=x AND f(x)!=x  :  {'UNSAT (contradiction)' if r3 == unsat else 'SAT (unexpected)'}")
    print()


# ---------------------------------------------------------------------------
# Part (d) — 4 pts: Array Axioms
#
# Prove BOTH axioms (two separate solver checks):
#   (1) Read-over-write HIT:   i = j  →  Select(Store(a, i, v), j) = v
#   (2) Read-over-write MISS:  i ≠ j  →  Select(Store(a, i, v), j) = Select(a, j)
#
# [EXPLAIN] in a comment below: Why are these two axioms together sufficient
# to fully characterize Store/Select behavior? (2–3 sentences)
# ---------------------------------------------------------------------------
def part_d():
    a = Array('a', IntSort(), IntSort())
    i, j, v = Ints('i j v')

    print("=== Part (d) ===")

    # Axiom 1: Read-over-write HIT
    #   i = j  →  Select(Store(a, i, v), j) = v
    s1 = Solver()
    s1.add(Not(Implies(i == j, Select(Store(a, i, v), j) == v)))
    r1 = s1.check()
    print(f"Axiom 1 (hit):  {'Valid' if r1 == unsat else 'INVALID'}")

    # Axiom 2: Read-over-write MISS
    #   i ≠ j  →  Select(Store(a, i, v), j) = Select(a, j)
    s2 = Solver()
    s2.add(Not(Implies(i != j, Select(Store(a, i, v), j) == Select(a, j))))
    r2 = s2.check()
    print(f"Axiom 2 (miss): {'Valid' if r2 == unsat else 'INVALID'}")

    # [EXPLAIN] These two axioms fully characterize Store/Select because they cover
    # the only two possible relationships between indices i and j: either i = j or
    # i ≠ j. The hit axiom defines what happens when you read from the index you just
    # wrote to (you get the new value), and the miss axiom defines what happens when
    # you read from any other index (the array is unchanged). Together they specify
    # the result of Select(Store(a,i,v), j) for every possible j, leaving no ambiguity.
    print()


# ---------------------------------------------------------------------------
if __name__ == "__main__":
    part_a()
    part_b()
    part_c()
    part_d()
