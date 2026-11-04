# Exact repeated-variable NAND formula reconstruction

This is a restricted, ordinary mathematical algorithm with a tested executable implementation. It is not a Lean formalization, a general circuit minimization result, or a P versus NP solution. No novelty claim is made.

## Model and interface

`repeated_z_nand.reconstruct(mask, n, z_reads=2, limits=Limits(...))` uses ordinary variables x_0 through x_(n-1), each required to occur exactly once, and a distinguished positive variable z required to occur exactly `z_reads` times, where that count is 0, 1, or 2. The witness is a full binary NAND tree. Leaves are positive variables only; constants, NOT gates, complemented edges, and shared internal gates are not free primitives. NAND(z,z) is allowed.

Input bit n is z. Truth-mask bit a is the value at assignment a. Hence the lower 2^n bits are the z=0 slice and the next 2^n bits the z=1 slice. A witness has exactly n+z_reads-1 NAND gates. The tree encoding is `('x', i)`, `('z',)`, or `('nand', left, right)`.

The implementation accepts 0<=n<=12 and positive leaf rank. It reports REPRESENTABLE with an independently evaluated witness, NOT_REPRESENTABLE only after complete search, RESOURCE_LIMIT if a time/state/transition limit interrupts the search, or INVALID_INPUT for invalid dimensions, masks, or limits. A resource limit never becomes a negative mathematical result. The default local limits are ten seconds, 100,000 states and 1,000,000 transitions. For z_reads=0 the input still includes the z coordinate; both slices must be represented by the same z-free formula.

## State and recurrence

A state is (S,k,G0,G1). S is the exact syntactic set of ordinary variables, k is the exact count of z leaves, and each G_b is a full truth-table constraint on S or a whole-slice wildcard. S is never replaced with the semantic support of a constraint. Every witness uses each member of S once and z exactly k times. Rank is |S|+k.

The only rank-one bases are a positive ordinary variable and the positive leaf z. There is no empty-rank formula and no constant leaf. For a NAND root, partition S into disjoint labeled groups U and V and split k into k_left+k_right. Both child ranks must be positive, so each is smaller than the parent rank.

For each slice independently:

* A wildcard gives two wildcard child demands.
* If the specified parent has a nonempty zero set Z, it must be a Cartesian product over U and V. Its two projections are the uniquely forced sets on which the child functions equal one. Test the product exactly. The all-zero parent is the full-rectangle case and forces both children to one.
* If the specified parent is identically one, its zero set is empty. Since the ordinary-variable groups are disjoint, at least one child must be identically zero. Branch over (zero,wildcard) and (wildcard,zero).

These constants are constraints, never free circuit leaves. The recursion must construct actual positive-variable NAND syntax satisfying them. The Cartesian branches for both slices are combined into paired child states, preserving their shared syntax and exact z counts.

## Soundness, completeness, and memoization

Every legal transition has the universal composition property: ANY two witnesses satisfying the generated child states satisfy the parent state after NAND. For nonempty rectangles the child values are fixed. For an identically-one parent, a child demanded zero masks every possible value of its sibling. A parent wildcard imposes no condition. Leaf multisets add exactly.

Consequently, a memo entry can keep one witness per EXACT state. It must never answer a more specified query using a weaker wildcard entry. The wildcard pattern, syntactic S, and k are all part of the key.

For completeness, take a valid formula and pass demands down from the root. At a nonempty rectangle its actual child slices equal the forced projections. At an identically-one slice at least one actual child is identically zero; select that branch. At a wildcard pass wildcards. Each actual subtree satisfies its resulting paired state. Induction on rank shows that the algorithm finds some valid witness, which need not be the original subtree. The universal composition property makes that substitution safe.

Empty ordinary-variable groups have one assignment. Rank positivity then requires z leaves. In particular, S empty with k=1 permits z, while S empty with k=2 permits NAND(z,z). This handles the singleton-branch case F=NAND(z,B(z,Y)): the z=0 output is one, so B's hidden z=0 slice stays a wildcard rather than receiving an invented value.

## Polynomial truth-table bound

Let the original function have n ordinary variables and table length N=2^(n+1). Every specified demand on S is either constant or a signed cofactor of the original slice F_b. In a nonempty zero rectangle, fix a point of the opposite projection; the demanded factor is the complement of that cofactor of the parent. Thus the signed-cofactor family is closed. Wildcards and constants cover the masking cases.

Per slice and S, there are at most 2*2^(n-|S|)+3 demands. Including k=0,1,2, the total state count is at most

    3 * (4*5^n + 12*3^n + 9*2^n).

For a state on s variables, enumerating all root partitions and projecting/testing the tables uses O(poly(n)*4^s) work. Summation gives O(poly(n)*8^n), or O(poly(log N)*N^3). A deterministic ordered memo table also fits this conservative bound after logarithmic factors. Explicit stored demand tables use O(poly(n)*6^n) bits. The implementation uses ordinary Python dictionaries; the mathematical polynomial bound can use deterministic ordered lookup instead of assuming collision-free hashing.

The actual implementation is resource bounded; if its configured cap is reached, its output is RESOURCE_LIMIT rather than the unrestricted algorithm's eventual answer. Returned witnesses are checked on every row with direct Boolean NAND evaluation, including exact leaf multiplicities and gate count.

## Review and validation

The public-math Claude Code subscription response is saved in [claude-reconstruction/visible-response.md](claude-reconstruction/visible-response.md). It judged the recurrence sound and complete. A separate agent independently checked the ordinary argument and the state/work counts. These are mathematical reviews, not formal certificates. The Claude record uses model alias opus and effort high; no exact underlying model version is asserted. Its informational list price is not Anthropic API ledger spend.

Nine focused tests passed in 0.242 seconds. They compare all 824 truth-mask/read-count cases through three total input variables with independently enumerated full formula trees; check every representable four-input function plus a fixed mask grid; exercise the non-unate repeated-z fixture, hidden singleton slice, exact wildcard keys, syntactically demanded but ignored coordinates, positive leaves, repeated fanins, and invalid/resource outcomes. The independent tree counts for three ordinary inputs are 12, 120, and 840 for k=0,1,2. A separate exhaustive four-input comparison completed all 196,608 mask/read-count checks in 29.922146 seconds, with no mismatches. It accepted exactly 3, 15, and 58 distinct functions for k=0,1,2, matching independent formula enumeration. The COMPLETE_EXACT_MATCH artifact is `results/repeated-z-exhaustive-four-input.json`, with source hashes. This stronger finite experiment is separate from the nine fast regression tests.

Reproduce the focused tests with:

    python -B -m unittest continuation.test_repeated_z_nand -v

The shared-internal-signal DAG normalization and any assembler using this module are separate work. This module alone recognizes the stated tree class.
