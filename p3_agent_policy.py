"""
CS292C Homework 2 — Problem 3: Agent Permission Policy Verification (25 points)
=================================================================================
Encode a realistic agent permission policy as SMT formulas and use Z3 to
analyze it for safety properties and privilege escalation vulnerabilities.
"""

from z3 import *

# ============================================================================
# Constants
# ============================================================================

FILE_READ = 0
FILE_WRITE = 1
SHELL_EXEC = 2
NETWORK_FETCH = 3

ADMIN = 0
DEVELOPER = 1
VIEWER = 2

# ============================================================================
# Sorts and Functions
#
# You will use these to build your policy encoding.
# Do NOT modify these declarations.
# ============================================================================

User = DeclareSort('User')
Resource = DeclareSort('Resource')

role         = Function('role', User, IntSort())          # 0=admin, 1=dev, 2=viewer
is_sensitive = Function('is_sensitive', Resource, BoolSort())
in_sandbox   = Function('in_sandbox', Resource, BoolSort())
owner        = Function('owner', Resource, User)

# The core predicate: is this (user, tool, resource) triple allowed?
allowed = Function('allowed', User, IntSort(), Resource, BoolSort())


# ============================================================================
# Part (a): Encode the Policy — 10 pts
#
# Encode rules R1–R5 from the README as Z3 constraints.
#
# You must design the encoding yourself. Consider:
# - Use ForAll to make rules apply to all users/resources.
# - Encode both what IS allowed and what is NOT allowed.
# - Rule R4 overrides R3 — handle this carefully.
#
# Return a list of Z3 constraints.
# ============================================================================

def make_policy():
    """
    Return a list of Z3 constraints encoding rules R1–R5.

    TODO: Implement this. You need to think about:
    1. How to express "viewers may ONLY do X" (everything else is denied).
    2. How R4 overrides R3 for admins.
    3. Whether you need a closed-world assumption (if not explicitly
       allowed, it's denied).
    """
    u = Const('u', User)
    r = Const('r', Resource)
    t = Int('t')

    constraints = []

    # Default deny: if not explicitly allowed by a rule, access is denied.
    # We encode each rule as: allowed(u, t, r) == True IFF one of the rule conditions holds.
    # The "allowed" predicate is True exactly when at least one rule grants access.

    # Build the "granted" condition: the disjunction of all rule antecedents.
    # R1: Viewers may only file_read non-sensitive resources.
    r1 = And(role(u) == VIEWER, t == FILE_READ, Not(is_sensitive(r)))

    # R2: Developers may file_read anything, and file_write resources they own or in sandbox.
    r2_read = And(role(u) == DEVELOPER, t == FILE_READ)
    r2_write = And(role(u) == DEVELOPER, t == FILE_WRITE,
                   Or(owner(r) == u, in_sandbox(r)))
    r2 = Or(r2_read, r2_write)

    # R3: Admins may use any tool on any resource (but R4 overrides for shell_exec on sensitive).
    r3 = And(role(u) == ADMIN, Not(And(t == SHELL_EXEC, is_sensitive(r))))

    # R4: Nobody may shell_exec on sensitive resources. (This is handled by excluding
    # shell_exec+sensitive from every rule, including R3 above.)

    # R5: network_fetch is allowed only on sandbox resources.
    # This is a restriction: network_fetch on non-sandbox is always denied.
    # We handle this by adding the sandbox requirement to all network_fetch grants.
    r5_restriction = And(t == NETWORK_FETCH, Not(in_sandbox(r)))

    # Combined: allowed iff granted by some rule AND not blocked by R4 or R5.
    granted = Or(r1, r2, r3)
    r4_block = And(t == SHELL_EXEC, is_sensitive(r))

    constraints.append(ForAll([u, t, r],
        allowed(u, t, r) == And(granted, Not(r4_block), Not(r5_restriction))
    ))

    return constraints


# ============================================================================
# Part (b): Policy Queries — 8 pts
# ============================================================================

def query(description, policy, extra):
    """Helper: check if extra constraints are SAT under the policy."""
    s = Solver()
    s.add(policy)
    s.add(extra)
    result = s.check()
    print(f"  {description}")
    print(f"  -> {result}")
    if result == sat:
        m = s.model()
        print(f"    Model: {m}")
    print()
    return result


def part_b():
    """
    Answer the four queries from the README.
    For query 4, also demonstrate what becomes possible without R4.

    TODO: Implement each query.
    """
    policy = make_policy()
    print("=== Part (b): Policy Queries ===\n")

    u = Const('u', User)
    r = Const('r', Resource)

    # Q1: Can a developer write to a sensitive file they don't own, in the sandbox?
    # [EXPLAIN] YES (SAT): R2 allows devs to file_write sandbox resources even if sensitive,
    # because R2 permits writes to resources they own OR in sandbox. Sensitivity doesn't block writes.
    query("Q1: Developer write sensitive, not-owned, sandbox file?", policy, [
        role(u) == DEVELOPER,
        is_sensitive(r) == True,
        in_sandbox(r) == True,
        owner(r) != u,
        allowed(u, FILE_WRITE, r) == True,
    ])

    # Q2: Can an admin network_fetch a resource outside the sandbox?
    # [EXPLAIN] NO (UNSAT): R5 blocks all network_fetch on non-sandbox resources for everyone.
    query("Q2: Admin network_fetch outside sandbox?", policy, [
        role(u) == ADMIN,
        in_sandbox(r) == False,
        allowed(u, NETWORK_FETCH, r) == True,
    ])

    # Q3: Is there ANY role that can shell_exec on a sensitive resource?
    # [EXPLAIN] NO (UNSAT): R4 blocks shell_exec on sensitive resources for all roles.
    query("Q3: Any role shell_exec on sensitive resource?", policy, [
        is_sensitive(r) == True,
        allowed(u, SHELL_EXEC, r) == True,
    ])

    # Q4: Remove R4 — what dangerous action becomes possible?
    # [EXPLAIN] Without R4, admins can shell_exec on sensitive resources (R3 is no longer overridden).
    u2 = Const('u2', User)
    r2_ = Const('r2_', Resource)
    t2 = Int('t2')

    r1_no4 = And(role(u2) == VIEWER, t2 == FILE_READ, Not(is_sensitive(r2_)))
    r2_read_no4 = And(role(u2) == DEVELOPER, t2 == FILE_READ)
    r2_write_no4 = And(role(u2) == DEVELOPER, t2 == FILE_WRITE,
                       Or(owner(r2_) == u2, in_sandbox(r2_)))
    r3_no4 = And(role(u2) == ADMIN)
    r5_no4 = And(t2 == NETWORK_FETCH, Not(in_sandbox(r2_)))
    granted_no4 = Or(r1_no4, r2_read_no4, r2_write_no4, r3_no4)

    allowed_no_r4 = Function('allowed_no_r4', User, IntSort(), Resource, BoolSort())
    policy_no_r4 = [ForAll([u2, t2, r2_],
        allowed_no_r4(u2, t2, r2_) == And(granted_no4, Not(r5_no4))
    )]

    u3 = Const('u3', User)
    r3_ = Const('r3_', Resource)
    query("Q4: Without R4, admin shell_exec on sensitive resource?", policy_no_r4, [
        role(u3) == ADMIN,
        is_sensitive(r3_) == True,
        allowed_no_r4(u3, SHELL_EXEC, r3_) == True,
    ])


# ============================================================================
# Part (c): Privilege Escalation — 7 pts
#
# New rule R6: Developers may shell_exec on non-sensitive sandbox resources.
#
# Attack scenario: A developer uses shell_exec on a non-sensitive sandbox
# resource to change ANOTHER resource's sensitivity flag (e.g., modifying
# a config file that controls access). This makes a previously sensitive
# resource become non-sensitive, bypassing R4 on the next step.
#
# Model this as a 2-step trace where a resource's sensitivity changes
# between steps.
# ============================================================================

def part_c():
    """
    TODO:
    1. Add rule R6 to the policy.
    2. Model a 2-step trace:
       - Step 1: developer calls shell_exec on resource r1
         (r1 is non-sensitive and in sandbox — allowed by R6)
         Side-effect: this command changes resource r2 from sensitive to
         non-sensitive (e.g., modifying an access-control config)
       - Step 2: developer calls shell_exec on resource r2
         (r2 is NOW non-sensitive — was it allowed before? is it allowed now?)
    3. The twist: r2's sensitivity changes BETWEEN steps. Encode this by
       using two copies of is_sensitive (before and after).
    4. Check if the developer can effectively access a previously-sensitive resource.
    5. [EXPLAIN] in a comment: Propose and implement a fix.
    """
    print("=== Part (c): Privilege Escalation ===\n")

    u = Const('u', User)
    r1 = Const('r1', Resource)   # the config resource (non-sensitive, sandbox)
    r2 = Const('r2', Resource)   # the target resource (originally sensitive)

    is_sensitive_before = Function('is_sensitive_before', Resource, BoolSort())
    is_sensitive_after = Function('is_sensitive_after', Resource, BoolSort())
    in_sandbox_esc = Function('in_sandbox_esc', Resource, BoolSort())

    # R6: Developers may shell_exec on non-sensitive sandbox resources.
    # Step 1: dev calls shell_exec on r1 (non-sensitive, in sandbox) — allowed by R6.
    step1_allowed = And(
        role(u) == DEVELOPER,
        Not(is_sensitive_before(r1)),
        in_sandbox_esc(r1),
    )

    # Side-effect: shell_exec on r1 changes r2 from sensitive to non-sensitive.
    r2_originally_sensitive = is_sensitive_before(r2)
    side_effect = Not(is_sensitive_after(r2))

    # Everything else keeps its sensitivity.
    r_any = Const('r_any', Resource)
    sensitivity_frame = ForAll([r_any],
        Implies(r_any != r2, is_sensitive_after(r_any) == is_sensitive_before(r_any)))

    # Step 2: dev calls shell_exec on r2 — now non-sensitive per is_sensitive_after.
    # R6 allows this if r2 is non-sensitive (after) and in sandbox.
    step2_allowed = And(
        role(u) == DEVELOPER,
        Not(is_sensitive_after(r2)),
        in_sandbox_esc(r2),
    )

    # r1 and r2 are distinct
    distinct = r1 != r2

    s = Solver()
    s.add(step1_allowed)
    s.add(r2_originally_sensitive)
    s.add(side_effect)
    s.add(sensitivity_frame)
    s.add(step2_allowed)
    s.add(distinct)

    result = s.check()
    print(f"  Escalation possible? {result}")
    if result == sat:
        print(f"  Model: {s.model()}")
    print()

    # [EXPLAIN] Fix: Add an immutability constraint — shell_exec cannot change
    # sensitivity flags. We enforce that is_sensitive_after == is_sensitive_before
    # for ALL resources, regardless of what shell_exec does.
    print("  --- Applying fix: immutable sensitivity flags ---")

    s2 = Solver()
    r_fix = Const('r_fix', Resource)
    immutable_sensitivity = ForAll([r_fix],
        is_sensitive_after(r_fix) == is_sensitive_before(r_fix))

    s2.add(step1_allowed)
    s2.add(r2_originally_sensitive)
    s2.add(side_effect)
    s2.add(immutable_sensitivity)
    s2.add(step2_allowed)
    s2.add(distinct)

    result2 = s2.check()
    if result2 == unsat:
        print("  ESCALATION BLOCKED")
    else:
        print(f"  Still possible: {s2.model()}")
    print()


# ============================================================================
if __name__ == "__main__":
    part_b()
    part_c()
