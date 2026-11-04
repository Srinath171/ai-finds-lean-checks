# Independent audit of Muse's gate-oracle follow-up

Reviewed only the saved public `visible_text` in `jobs/gate-oracle-followup/state.json`. These are independently AI-reviewed mathematical conclusions, not a newly compiled Lean theorem, human review, or novelty claim. No model calls or source exports were made. The main exact scalarization and P versus NP remain unsolved.

## Reverse reduction: verified

Let A decide J(f,NAND(x_i,x_j))<=s, with the second component restricted to one NAND of original inputs, and let B be ordinary total NAND-MCSP. For n>=1, B reduces to A by polynomial-time Turing queries.

If f is a projection, C(f)=0 and the answer is immediate. Otherwise an optimal f-circuit has at least one gate. A topologically first gate uses only original inputs, so it is some NAND(x_i,x_j), including repeated fanins. The circuit itself supplies both f and that gate function. Since every joint circuit also computes f,

    min_(i,j) J(f,NAND(x_i,x_j)) = C(f).

Thus C(f)<=s iff one of the at most n^2 joint queries accepts. Truth tables have length N=2^n; generating and writing the queries costs polynomially many bits in N and the threshold encoding. An A-oracle therefore yields the numerical optimum and a possible first gate of an optimal circuit. It does not yet yield every subsequent gate.

## Multi-feature search: verified with explicit scope

E(f;W) is the minimum additional NAND cost with the total n-input functions W available as free generators, evaluated on the ORIGINAL input x. The generators need not be independent. This is a conditional/graph predicate, not ordinary total MCSP on all independent assignments to n+|W| inputs.

An E-oracle first obtains s=C(f)=E(f;empty) by binary search up to the constructive bound B(n)=O(N log N). Maintain an actual k-gate prefix W and E(f;W)<=s-k. A minimum residual circuit, unless f is already a source, has a first gate h=NAND(u,v) among current sources. Removing it gives E(f;W,h)<=s-k-1. Enumerating all source pairs and querying this predicate therefore finds an extension.

Semantic duplicates can be explicitly skipped. With the optimal initial s they cannot pass a strictly smaller residual budget anyway: a duplicate adds no new free function, and E(f;W)<s-k would compose with the selected prefix to contradict C(f)=s. At k=s the residual budget is zero, so f must be an available source. This proves termination and optimality.

There are at most s stages, O((n+s)^2) candidates per stage, and O((s+2)N+log(s+2)) query bits each. Since s<=B(n), oracle calls, classical work and total truth-table writing are polynomial in N. Constants are paid gates, and n=0 is excluded. These details complete omissions in the short presentation without changing its conclusion.

A fresh narrow-A query cannot encode this growing conditioned state: its second function must be one NAND of original inputs, and its answer does not jointly constrain every previous choice. The arbitrary-output search lemma elsewhere uses a stronger common-witness oracle, not an implicit implementation of E or narrow A by B.

## Constant-one incompatibility: verified

For two inputs, f=1 has cost two: NOT x followed by NAND(x,NOT x). No primary or one-NAND output is constant one. Put a=NOT x and b=NOT y. Each pair (f,a) and (f,b) has joint cost two, but (f,a,b) has cost three. The lower bound is immediate because these are three distinct noninput functions and two gates supply only two noninput wire functions.

Equivalently E(f;{b})<=1, but E(f;{a,b})<=0 is false. Thus separate feasible singleton choices cannot be combined without a common-witness condition. The actual next gate after a in the displayed optimal circuit computes constant one, which is not any NAND of the two original primary inputs.

The related claim J(1,NAND(x,y))=3 is also correct. If NAND(x,y) is first, the six possible second-gate functions are NOT x, NOT y, NAND(x,y), NOT x OR y, x OR NOT y, and x AND y; none is one. If it is second, no earlier output is one. The three-gate construction supplies the matching upper bound. Root separately replayed the finite examples; this review does not claim a new formalization of them.

Inspecting one arbitrarily returned optimal circuit is insufficient to decide incidence: an optimal constant-one circuit using NOT x may omit NOT y, even though another optimal circuit contains it. This refutes that inspection method, not every adaptive use of an optimal-search oracle.

## Conditional search equivalences: verified, with a required correction

Define SR_B as polynomial truth-table-time optimal search using only B, and SR_A analogously using A. Because B<=T^p A, simulating each B-query establishes

    SR_B implies SR_A.

If the additionally sought A<=T^p B reduction exists, simulating each A-query also establishes

    SR_A implies SR_B.

Both compositions preserve polynomial time and total query-writing length because each intermediate truth table already has polynomial length. Under that extra reduction, the two search statements are equivalent.

**Unsupported wording in Muse's report:** “Without the sought reduction, SR_A would not imply SR_B” asserts a nonimplication that has not been proved. The correct statement is: **these arguments establish no reverse implication without an additional reduction or simulation.** Extra oracle information is a reason the displayed proof does not work, not a proof that no other implication exists.

Also, A<=T^p B by itself proves oracle equivalence with B but does not establish SR_A, SR_B, or a complete search algorithm. No converse equating existence of that scalarization with existence of an unconstrained search-to-decision algorithm was proved. The final list of research routes is an approach-specific roadmap, not an exhaustive impossibility dichotomy.

## Current outcome

The reverse reduction, conditioned-generator search procedure, compatibility counterexamples, and stated conditional oracle compositions are mathematically sound with the clarifications above. The crucial unresolved step is still a proved simulation of narrow A or the growing conditioned predicate by the allowed ordinary single-output MCSP oracle. No unconditional circuit-complexity or P-versus-NP conclusion follows.
