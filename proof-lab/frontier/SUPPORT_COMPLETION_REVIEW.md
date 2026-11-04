# Support-based completion: valid conditional reduction and its missing premise

This note concerns one proposed route from a structured partial NAND-circuit problem to ordinary total truth-table MCSP. It is not a reduction for arbitrary Partial MCSP and not a P versus NP result.

## Exact restricted problem

Let D be the N graph rows of a fixed one-gate prefix on M=n+1 coordinates, with labels f(x). Fix a nonempty coordinate set S, k=|S|. Project every labelled row to S. If two projected rows have different labels, no total extension depending only on S exists. Otherwise let h(S)=2^k minus the number of distinct projected rows.

Enumerate all 2^h(S) assignments to the unspecified projected patterns. For each completed k-input truth table H, query total NAND-MCSP(H,t), using the SAME threshold t. Any yes answer lifts its circuit to the original M inputs by replacing each primary input with the corresponding selected coordinate, without adding gates. This proves unconditional soundness.

Conversely, if a cost-at-most-t extension depends only on S, semantic independence lets us replace every excluded primary input by any retained input and renumber the gate wires. This preserves the gate count, including DAG sharing and output selection. The resulting k-input function is one of the enumerated completions, so a query is yes. The independent circuit transformation is formalized in CircuitRewiring.lean; the enumeration algorithm and its complexity accounting are a mathematical argument here.

A constant extension has empty semantic support, but circuit arity zero has no legal primary signal in this basis. It can be represented using any one original coordinate instead: substitute all inputs by that coordinate. On the full one-gate graph, this original coordinate takes both values, giving no projected holes. The algorithm uses nonempty coordinate sets throughout.

For a family F of candidate supports, this exactly decides whether the RESTRICTED optimum e_F is at most t. It decides the unrestricted optimum e at every threshold only with an additional completeness promise, for example e_F=e. That promise is not supplied by the enumeration itself.

## Query and writing bounds

There are 2^M=2N coordinate subsets for a one-gate graph. For fixed c, retaining only sets with h(S)<=c*n gives at most N^c completions per support and at most 2N bits per query table. The number of queries is at most 2*N^(c+1); the total table bits written are at most 4*N^(c+2), apart from threshold encoding and polynomial projection work. Thus the conditional reduction really is polynomial in N and log(t+2).

More generally, a supplied polynomial-size support family with O(log N) holes per set suffices. A qualifying table has size 2^|S|=|projected D|+h(S)<=N+h(S); it need not be small merely because its support has constant cardinality. The useful hypothesis is the number of holes and a support-completeness promise.

## General counterexample to an automatic optimal-support promise

For each n>=2 choose the cheaper NAND phase of parity and its complement, with optimal cost C. Both phases have finite minimum cost and are not projections. Delete an optimal circuit's first NAND gate p. The optimum residual extension cost is exactly e=C-1: deletion proves the upper bound; prefixing p to a cheaper extension contradicts C.

Every residual extension of cost at most C-1 must depend on the auxiliary coordinate z. Otherwise remove z by zero-cost input substitution and obtain an n-input circuit for the chosen phase costing less than C.

If p=NAND(x_i,x_j) has distinct fanins, every original input is essential already on the graph: flip an unrelated input while holding the prefix fixed; for fanin x_i hold x_j=false, and conversely. Parity changes while z stays fixed.

If p=NOT x_i, all other originals remain essential. If an extension ignored original x_i, its remaining n coordinates, including z, parametrize the full cube on the graph z=NOT x_i. Substituting away the ignored coordinate gives a circuit for the OPPOSITE parity phase with at most C-1 gates. This contradicts choosing the cheaper phase.

Thus every optimal extension depends on all M coordinates. Every supporting coordinate set is the full set, whose graph has exactly N=2^n holes. For each fixed c, choose n with 2^n>c*n. The automatic bounded-hole optimum-support promise fails. This proof does not assume an exact parity circuit-size formula or a direct-sum theorem. The phase and first gate are existentially selected by optimal size; no polynomial-time selector is claimed.

The general argument passed two independent mathematical audits, a Muse Wonder MAX audit, and a regular Claude Code audit. OptimalSupport.lean now formalizes the both-phase minimum, exact residual budget, total essential support, exact missing rows, and arbitrarily large violations of every fixed linear cap. CircuitRewiring.lean and GraphHoles.lean provide the checked transformations and counts. Consult the current verification report for exact compiled source hashes. The separate exact n=2 support_holes.py experiment checks the XOR instance without extrapolating finite data to the general statement.

## What survives

The restricted-support completion algorithm remains sound and complete for its own optimum. Gap-promise algorithms can also survive an additive cost overhead. This obstruction rules out the automatic support premise and its exact unchanged-threshold completion shortcut. It does not rule out other gadgets, adaptive oracle reductions, input-dependent global completions, approximation promises, or all MCSP self-reductions.


## Model-audit review

The public Muse and Claude outputs are saved in results/optimal-support-proposals.json with model-output status, separately from the formal sources and their verification evidence. Both accepted the main argument under total semantic support and exact residual budget.

Claude's suggested change from x_0 to x_1 is not needed: this project consistently uses zero-based coordinates 0 through n-1. Its arity-only reason for excluding a source gate as the final parity output also needs n>2; at n=2, the direct NAND truth function, rather than arity alone, excludes both parity phases. Neither observation is used by the formal proof, which handles output selectors directly.

Graph-relative support is a different condition. Original x-coordinates always determine the observed labels and have zero projected holes. That fact does not let us remove a useful free NAND coordinate from an exact-budget circuit without paying for its computation. The formal theorem and cost-preserving removal lemma use independence on the TOTAL function, including unspecified rows.
