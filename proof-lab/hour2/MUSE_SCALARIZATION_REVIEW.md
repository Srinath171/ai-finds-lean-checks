# Independent review of Muse's scalarization gap report

Scope: read only `jobs/scalarization-meta-v2/state.json`'s `visible_text`, containing public mathematics, and audit the stated model. This is independent AI mathematical review, not human review, accepted peer review, or a new Lean proof. No model calls, source export, credentials, or other job data were used. The exact scalarization and P versus NP remain unsolved.

## 1. Verified: joint cost and the two-query boundary

Let C(f) be single-output NAND cost, J(f,g) shared two-output cost, and g=NAND(x_i,x_j), with n>=1 and repeated fanins allowed. Let e(f,g) be graph-consistent extension cost using one extra free primary input z. The identity J=e+1 is correct.

For the lower direction, the designated g-output cannot be an original input projection, so it is a gate. Delete it, replace all its outgoing uses and any matching output selector with the new primary z, and renumber remaining wires. On z=g(x), all surviving gate values agree with the original computation. Existing sharing is preserved, and there are at most one fewer gates. Computing g once and then an extension gives the converse bound. This handles f=g and arbitrary topological positions of the designated gate.

The interval C(f)<=J<=C(f)+1 is correct. Queries C(f)<=s-1 (only for s>=1) and C(f)<=s decide yes when C(f)<=s-1 and no when C(f)>s. The numerical boundary is C(f)=s. Thresholds at least B(n)+1 are trivially yes under the supplied universal bound; s=0 has no joint yes instance because g is not a projection. Boundary cases need not all be hard: C(f)=0 and f=g can be handled directly.

At the nontrivial boundary, J=s means an optimal f-circuit can also produce g as a wire; otherwise J=s+1. Numeric C(f) alone does not supply a circuit witness or this incidence information.

## 2. Verified: syntactic gate normalization

If an existing gate computes g, replacing its two fanins by the original primary inputs x_i,x_j is safe. Both are earlier legal wires, so acyclicity and well-formedness remain intact. The gate's total Boolean function remains g, hence all downstream functions remain unchanged. Keeping now-unused predecessors preserves the gate count; pruning could only decrease it. This does not reveal that gate to a decision-only MCSP oracle, and therefore does not close the reduction.

## 3. Verified: mux costs and the exact XOR lower bound

For H(x,b)=f(x) when b=0 and g(x) when b=1, Muse's n=1 examples are correct. If f=g=NOT x, then J=1 and C(H)=1. If f=x and g=NOT x, then J=1 but H=x XOR b has NAND cost exactly four.

The four-gate construction is standard and correct. For the lower bound with at most three gates, trim gates after the output and make it the last gate. Its two inputs must both be one at 00 and 11 because their conjunction is XNOR. Neither primary input is one at 00, and none of the three possible first-gate functions NOT x, NOT b, NAND(x,b) is one at 11. Thus, if three gates were available, both output fanins would have to be the second gate. That gate would need to be XNOR. Its fanins would both have to be one at 01 and 10; among available primary/first-gate wires only NAND(x,b) could do that, whose repeated AND is not XOR. Contradiction.

The fixed-offset contradiction is correct even at fixed n=1: the first example at s=0 forces offset d<1; the second at s=1 forces d>=3. It excludes this mux with one universal additive threshold offset. It does not exclude an input-dependent calibration algorithm, another gadget, or adaptive queries.

## 4. Verified: parity-copy candidate, with a stronger obstruction

For fixed t>=1, define F_t as parity of the t f-values on disjoint input copies, G_t as parity of the t g-values, and H_t as their shared-selector mux. Its table has 2*N^t bits. Concatenating t joint circuits, two parity trees and one mux gives

    C(H_t) <= t J + 8t - 4.

Thus the proposed threshold is kappa = t*s + 8t - 4. For t=2 this is 2s+12, and exactness for all thresholds would require C(H_2)>=2J+11 in every no-at-s=J-1 case. Muse correctly refutes that bound with n=1, f=x, g=NOT x, J=1, s=0. Even t gives parity of the t originals, costing at most 4(t-1); odd t adds the selector to that parity, costing at most 4t. These are upper bounds, not asserted optimum parity sizes.

**Minor wording correction:** for t=1 the odd-case cost bound 4t equals the threshold 8t-4 rather than being strictly below it. The false positive still occurs because the oracle accepts equality. No substantive counterexample conclusion changes.

Letting t grow without a fixed bound generally destroys the required polynomial writing bound N^t; amplification cannot hide that cost.

**New stronger counterexample, verified independently.** Merely preprocessing projections or restricting to C(f)=s>0 does not repair this parity gadget. Take n=2,

    f(x,y)=NOT x, g(x,y)=NAND(x,y), s=C(f)=1.

Both desired outputs are distinct nonprojection functions. One gate supplies only one noninput wire, so J>=2; the two direct NAND gates give J=2. This is a genuine no instance J>s at the numerical boundary, with f neither a projection nor g.

For one copy and common selector b, the mux function is

    h(x,y,b) = NOT x OR (b AND NOT y).

It has the following three-gate NAND implementation, with every negation paid:

    r = NAND(y,y), u = NAND(b,r), h = NAND(x,u).

Pointwise, the parity-selector H_t equals XOR_k h(x^k,y^k,b): when b is fixed, all copies select the same branch. Computing these t three-gate muxes followed by a parity tree therefore gives

    C(H_t) <= 3t+4(t-1) = 7t-4.

But the proposed threshold at s=1 is 9t-4. It accepts for every fixed t>=1, while J=2>s. This strengthens Muse's obstruction and survives the suggested trivial-boundary preprocessing. It refutes only this parity-selector construction, not every possible fixed function Phi or every adaptive reduction.

## 5. Verified conditional implication; unproved forcing premise

Muse's Exact Forcing Lemma is logically sufficient as stated, provided D is a nonnegative gate-count bound and t,q are fixed constants. If an explicit fixed Phi has a D-gate circuit and uniformly satisfies

    tJ + A <= C(H_Phi) <= tJ + D, with D-A<t,

then threshold kappa=t*s+D is exact: yes instances meet its upper bound, while J>=s+1 gives C(H_Phi)>=t*s+t+A>kappa. The table size 2^q*N^t is polynomial for fixed t,q, and its bits can be generated from the input tables without knowing a circuit for f. Feasibility of the displayed interval also implies A<=D; A itself need not be nonnegative.

The upper inequality follows by concatenating the t joint computations and the given Phi circuit. The lower inequality is the unproved content. Neither output restrictions, copy independence, semantic wire names, nor known upper bounds establish it against arbitrary shared DAGs. No direct-sum lower bound is being proved by the upper construction.

The inequality D-A<t is sufficient for this fixed-scale, fixed-offset family, not a necessary condition for arbitrary scalarizations. Other threshold maps, non-compositional constructions and multiple adaptive queries need not fit that interval. No impossibility result for those alternatives follows.

## 6. What remains, and what counts as a repair

No exact reduction is established. The bridge and the numerical boundary are valid; both mux candidates fail, and the stronger counterexample above prevents repairing the parity candidate merely by excluding projections and f=g.

A weaker but still substantive future target is an exact separator only on the already isolated boundary C(f)=s>=1. It would need to derive, from any accepted scalar-query circuit or proven query-answer pattern, a shared circuit for f,g of at most s gates. That conditional decoding claim need not assert a global direct-sum law, but it must actually be proved for a specified query family. It is a target, not a verified repair. No such decoder, separator, Phi or complete oracle algorithm is supplied by Muse or by this review.

All positive statements above concern the exact NAND model and global Boolean truth tables. They do not import a different basis's costs, circuit witnesses from a decision oracle, a partial-table oracle, or a separation theorem. P versus NP, general MCSP hardness, and the exact requested scalarization remain unsolved.


## 7. Further independent result: unbounded counterfamily and an exact subclass classifier

**Verified independently by AI, not Lean-formalized.** Let r>=1, let h(u_1,...,u_r) be a read-once NAND tree with r-1 gates (for r=1, take h=u_1), and put

    f = NAND(x,h), g = NAND(x,y), s=r.

Every input of h is essential, by induction through its read-once tree, and h attains both Boolean values. Thus f has r+1 essential inputs and an r-gate construction. The single-output essential-input bound gives C(f)>=r, so C(f)=r=s.

The joint function has r+2 essential input nodes. Its two output cones share the essential input x. After pruning gates irrelevant to both outputs, their union is a connected undirected graph: each cone is connected to its output, and the two cones meet on a path from x. If it has S gates, its binary fanins supply at most 2S edges counted with multiplicity, while connectivity requires at least (S+r+2)-1 distinct edges. Therefore S>=r+1. Computing h, f and g gives that upper bound as well, so J=r+1>s.

A single selected-copy mux satisfies the identity

    mux_b(f,g) = NAND(x, mux_b(h,y)).

The r-1 gates for h, four for the inner mux, and one final NAND give cost at most r+4. As before, a shared-selector mux of the two parities equals parity of the per-copy muxes. Consequently

    C(H_t) <= t(r+4)+4(t-1) = tr+8t-4 = kappa

at the no-instance threshold s=r, for every fixed t>=1. Setting x=1 makes (f,g)=(NOT h,NOT y), so all four output-value pairs occur. This counterfamily survives restriction to positive boundary cost, nonprojection targets, full pair range, and exclusion of any fixed finite range of small costs. It does not rule out arbitrary polynomial preprocessing; in fact the following preprocessor detects it.

**Exact subclass classifier.** From the truth table, compute the essential-input set S_f and d=|S_f|. Suppose the numeric boundary is C(f)=s=d-1, and g=NAND(x_i,x_j) uses one essential coordinate and one nonessential coordinate. Then

    J(f,g)=d=s+1.

For the lower bound, the two relevant output cones share the essential coordinate, so their pruned union is connected. It contains at least d+1 essential input nodes in total; the same edge count forces at least d gates. The upper bound is C(f)+1=d. Hence this boundary instance is exactly NO for J<=s.

Testing essential inputs takes O(n*2^n) direct truth-table comparisons, with ordinary indexing-bit overhead still polynomial in N=2^n. This is a proved local classification rule that can be added to the two-query protocol without assuming any direct-sum law or receiving circuit witnesses. It is not a complete scalarization, and it says nothing about boundary inputs outside its hypotheses. The strengthened parity counterfamily demonstrates why its proposed threshold fails, while this classifier supplies a genuine limited repair rather than an assertion that every preprocessing scheme fails.
