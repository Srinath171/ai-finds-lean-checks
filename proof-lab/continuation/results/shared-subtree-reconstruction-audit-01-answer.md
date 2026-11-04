## Verdict

Conditional on the stated soundness, completeness, reconstruction, and runtime interfaces of **RO** and **TWICE**, the outer theorem is correct. No fatal gap occurs in the reduction. The uses of those subroutines match their interfaces, including the singleton and empty-\(Y\) cases. This audit does not re-prove RO or TWICE.

Here \(f\) is nonconstant on exactly \(d\ge 1\) essential variables. Count every fanin occurrence separately.

### A. Graph counting and the shared-signal decomposition

Take a minimum circuit and retain only ancestors of its selected output. This does not increase its gate count. All \(d\) primaries remain, since \(f\) depends essentially on each. Let the pruned circuit have \(s\) gates.

There are \(d+s\) signal vertices and \(2s\) fanin occurrences. The output has outdegree \(0\); every other retained signal has outdegree at least \(1\), because it lies on a path to the output. Hence
\[
2s\ge d+s-1,\qquad s\ge d-1.
\]

If \(s=d-1\), equality forces every nonoutput signal to have outdegree exactly \(1\). Thus there is no sharing and no repeated fanin: a repeated fanin or two uses would contribute outdegree \(2\). The circuit is physically a read-once NAND tree with \(d\) leaves and \(d-1\) gates. This also covers \(d=1,s=0\), where the tree is the positive projection.

If \(s=d\), then
\[
\sum_{\text{nonoutputs}}(\operatorname{outdeg}-1)
=2d-(2d-1)=1.
\]
Consequently exactly one nonoutput signal \(q\) has outdegree \(2\), and every other nonoutput signal has outdegree \(1\).

Let \(A\) be the ancestor set of \(q\), including \(q\). Suppose \(A\) contains \(w\) primaries and \(g\) gates. For \(a\in A\setminus\{q\}\), a path from \(a\) to \(q\) must begin with \(a\)'s sole outgoing occurrence; hence that occurrence leads to another member of \(A\), ultimately to \(q\). Therefore no gate or primary in \(A\setminus\{q\}\) has a direct use outside \(A\): all exit from \(A\) is through \(q\).

The \(g\) gates in \(A\) have \(2g\) fanin occurrences, all originating in \(A\). Counting those occurrences by source, each member of \(A\setminus\{q\}\) contributes \(1\), while \(q\) contributes \(0\) inside \(A\) by acyclicity. Thus
\[
2g=(w+g)-1,\qquad g=w-1.
\]
Also \(w\ge1\), since following fanins from \(q\) reaches a primary. A repeated fanin inside \(A\) would give its source two internal uses, impossible unless that source were \(q\), which would create a cycle. Hence \(A\) is a strict full binary read-once NAND tree on \(W\), with \(|W|=w\) and \(w-1\) gates.

Two qualifications handle the literal boundary wording:

- If \(q\) is a gate, primaries in \(W\) have no occurrence outside \(A\).
- If \(q\) is itself a primary, then \(A=\{q\}\), \(W=\{q\}\), and \(g=0\). Its two outside uses are precisely the two copies of the collapsed leaf \(z\) below.

Now collapse \(A\) to a formal leaf \(z=q\). The remaining gates number
\[
s-g=d-(w-1)=d-w+1=|Y|+1,
\qquad Y=\text{inputs}\setminus W.
\]
Every \(Y\)-primary has its sole use outside \(A\); \(q\) has exactly two outside uses; every remaining gate except the output has outdegree \(1\). Unfolding the two uses of \(q\) into two \(z\)-leaves therefore produces a genuine NAND formula \(H(z,Y)\), with no other duplication. Its leaves are \(z,z\) and each \(Y\)-variable once, so it has \(|Y|+2\) leaves and \(|Y|+1\) gates. The two \(z\)-uses may enter the same gate, giving \(\mathrm{NAND}(z,z)\), or two different gates; multiplicity counting covers both.

No ancestor of \(q\) can be used directly outside through a second edge, since that would make it the unique outdegree-\(2\) vertex instead of \(q\).

### B. Exact row recovery

For \(a\in\{0,1\}^W\) and \(b\in\{0,1\}^Y\), define the row
\[
R_a(b)=f(a,b).
\]
For the structural \(W\) above,
\[
R_a=H(q(a),\cdot).
\]
Thus there are at most two row types.

There are exactly two:

1. \(q\) is nonconstant. A read-once Boolean NAND tree is surjective by induction: at a root, choosing one surjective child to be \(0\) gives output \(1\), while choosing both children to be \(1\) gives output \(0\). Equivalently, constancy of \(q\) would make \(f\) independent of \(W\).
2. The two slices \(H(0,Y)\) and \(H(1,Y)\) are distinct. If they were equal, \(f\) would be independent of every variable in the nonempty set \(W\), contradicting the hypothesis that all \(d\) inputs are essential.

Hence both row types occur and are distinct. This is where essentiality and nonconstancy are used; a constant function could not have \(d\ge1\) essential inputs.

For either assignment of names \(0,1\) to the two observed row types, define \(H_L\) from those two rows and define
\[
q_L(a)=
\begin{cases}
0,&R_a\text{ is the type labeled }0,\\
1,&R_a\text{ is the type labeled }1.
\end{cases}
\]
Trying both labelings includes the labeling induced by the true decomposition. For that labeling, \(q_L\) is the actual read-once-tree function on \(W\), and \(H_L\) is the actual outside formula. Thus RO and TWICE are invoked on precisely the kinds of tables covered by their completeness interfaces.

No arbitrary truth table is guessed: \(W\) is enumerated, rows are read from \(f\), \(q_L\) is the observed row-class map, and \(H_L\) consists of the two observed rows. The only choices are the subset \(W\) and two bit-labelings.

### C. Soundness, cost, and optimality

Suppose, for some \(W\) and labeling, RO accepts \(q_L\) and TWICE accepts \(H_L\). By their soundness, the reconstructed objects compute exactly those tables. Wiring the single computed \(q_L\)-signal to both \(z\)-positions of the \(H_L\)-formula gives, for every \((a,b)\),
\[
H_L(q_L(a),b)=R_a(b)=f(a,b).
\]
Sharing \(q_L\)'s output is allowed and does not recount its gates.

The gate count is
\[
(|W|-1)+(|Y|+1)=|W|+|Y|=d.
\]
This remains valid when \(|W|=1\), where the \(q\)-tree is a zero-gate primary wire, and when \(Y=\varnothing\), where the \(H\)-part has one gate.

There is no free negation from the swapped labeling. The swapped pair consists of the exact complementary row-class function and the exact slice-swapped \(H\); RO and TWICE must realize those exact tables without complemented edges. Whether or not the swapped pair also happens to be realizable, composition still computes \(f\).

Optimality follows from the initial RO call. If RO accepts \(f\), it returns a \(d-1\)-gate tree, optimal by \(C(f)\ge d-1\). If RO rejects \(f\), no \(d-1\)-gate circuit exists: such a circuit would have the saturated tree form above and RO would accept it. Therefore a subsequently returned \(d\)-gate circuit is optimal. If all subsets fail and \(C(f)\le d\), then \(C(f)\) would have to be \(d-1\) or \(d\); the first is excluded by RO rejection, and the second would yield the structural \(W\) accepted by RO and TWICE. Hence rejection is correct.

### D. Boundary cases

- **\(d=1\).** The identity is accepted initially by RO as a zero-gate projection. For \(\neg x\), RO rejects; the only subset is \(W=\{x\}\), \(Y=\varnothing\). The correct labeling gives \(H(0)=1,H(1)=0\), \(q(x)=x\), and TWICE realizes \(H(z)=\mathrm{NAND}(z,z)\). The total is \(0+1=1\).

- **\(W\) all inputs, \(Y=\varnothing\).** Rows are scalars. TWICE is not permitted to return \(H(z)=z\), which has the wrong leaf multiset. Its only possible one-gate, two-\(z\)-leaf formula is \(\mathrm{NAND}(z,z)\). This is precisely the structural possibility that the outside part is one gate using \(q\) twice.

- **\(q\) a primary.** Then \(W\) is a singleton and RO accepts only the positive projection, not its negation. The complementary labeling is tested separately and cannot silently use a free NOT.

- **Repeated fanins.** They are counted with multiplicity throughout. Inside the \(q\)-tree they cannot occur in the \(s=d\) optimum except through the designated collapsed signal \(q\); in \(H\), \(\mathrm{NAND}(z,z)\) uses the two permitted \(z\)-occurrences.

- **Constants.** No constant leaves or complemented edges are introduced by the structural decomposition, RO, TWICE, or composition.

- **Ambient dummy inputs.** The stated model has exactly \(d\) wires, so this is not needed. If dummy wires were allowed with output required to equal \(f\) for every dummy assignment, replacing each dummy by \(x_1\) would preserve the output—each essential assignment selects an allowed dummy assignment—and pruning would not increase the gate count. Thus the required existence of an essential-only circuit with no more gates still holds.

### E. Runtime

Let \(w=|W|\) and \(|Y|=d-w\).

- Initial RO: \(\operatorname{poly}(d)6^d\).
- For a fixed \(W\), row grouping compares each of \(2^w\) rows, of length \(2^{d-w}\), with at most two representatives. With \(\operatorname{poly}(d)\) indexed-access cost, this is \(\operatorname{poly}(d)2^d\). Over all \(2^d\) subsets, the total is \(\operatorname{poly}(d)4^d\).
- There are at most two labelings per nonempty \(W\). RO calls contribute
  \[
  \sum_{w=1}^d \binom dw \operatorname{poly}(d)6^w
  =\operatorname{poly}(d)7^d.
  \]
- TWICE calls contribute
  \[
  \sum_{w=0}^d \binom dw \operatorname{poly}(d)8^{d-w}
  =\operatorname{poly}(d)9^d.
  \]
Constructing the \(2^w\)-entry \(q\)-table and \(2^{d-w+1}\)-entry \(H\)-table is dominated by these bounds.

Hence the total deterministic time is \(\operatorname{poly}(d)9^d\). The hypotheses are only subset-and-label choices—not a factorial enumeration, hashing assumption, or arbitrary truth-table search. The conclusion is explicitly conditional on RO and TWICE satisfying their stated interfaces.