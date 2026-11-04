# Muse Wonder MAX: one-reuse-rectangle-01

Status: finished; usage settled; recorded cost USD 0.208484. This is the visible model answer, independently reviewed in the companion review file.

## 1. Cofactor statement

**Lemma.** Every strict read-once NAND formula on a nonempty variable set is surjective.

Indeed, a variable is surjective. If \(F=\mathrm{NAND}(G,H)\), where \(G,H\) use disjoint nonempty variable sets and are surjective, assignments with \(G=H=1\) give \(F=0\), while an assignment with \(G=0\) gives \(F=1\).

**Proposition 1.** Let \(A(z,X)\) be strict read-once NAND, using exactly \(\{z\}\cup X\), with \(X\neq\varnothing\). For \(b\in\{0,1\}\), write \(A_b(X)=A(b,X)\). Then:

1. \(A_b\) is never identically \(0\);
2. \(A_b\equiv1\) iff \(b=0\) and \(z\) is a direct child of the root;
3. otherwise, \(A_b\) is nonconstant.

**Proof.** Induct on the number of leaves. If there are two leaves, \(A=\mathrm{NAND}(z,x)\) for \(X=\{x\}\). Then \(A_0\equiv1\) and \(A_1=\neg x\), proving the claim.

For more leaves, write the root as \(\mathrm{NAND}(S,T)\), where \(S\) contains \(z\) and \(T\) does not.

If \(S\) is the leaf \(z\), then \(T\) is a surjective formula on \(X\). Hence
\[
A_0=\mathrm{NAND}(0,T)\equiv1,\qquad A_1=\mathrm{NAND}(1,T)=\neg T,
\]
which is nonconstant. Neither is identically \(0\).

Otherwise, \(S\) has variables \(\{z\}\cup X_S\) with \(X_S\neq\varnothing\), and \(T\) has a nonempty variable set \(X_T\), disjoint from \(X_S\). By induction, \(S_b\) is either identically \(1\)—only in the special subcase inside \(S\)—or nonconstant; in either case it attains \(1\). Also \(T\) attains both values. Since the variable sets are disjoint:

- choosing \(S_b=1\) and \(T=1\) gives \(A_b=0\);
- choosing \(T=0\) gives \(A_b=1\).

Thus \(A_b\) is nonconstant in this case. This proves all three claims, including necessity of the stated condition for \(A_b\equiv1\). ∎

If \(X=\varnothing\), the statement fails: necessarily \(A=z\), so \(A_0\equiv0\) and \(A_1\equiv1\), although there is no root gate of which \(z\) is a direct child.

## 2. Rectangle reconstruction

**Proposition 2.** Let \(X,Y\) be disjoint nonempty sets. Let \(A(z,X)\) and \(B(z,Y)\) be strict read-once NAND formulas, and
\[
F(z,x,y)=\mathrm{NAND}(A(z,x),B(z,y)).
\]
Given the labeled partition \(X,Y\), both tables \(A\) and \(B\) are uniquely recoverable from the table of \(F\).

**Proof.** For fixed \(b\), let
\[
Z_b=\{(x,y):F(b,x,y)=0\},
\]
\[
U_b=\{x:A_b(x)=1\},\qquad V_b=\{y:B_b(y)=1\}.
\]
Since NAND outputs \(0\) exactly when both inputs are \(1\),
\[
Z_b=U_b\times V_b.
\]
By Proposition 1, \(A_b\) and \(B_b\) are either identically \(1\) or nonconstant, so both attain \(1\); hence \(U_b,V_b\), and \(Z_b\) are nonempty. A nonempty Cartesian product is recovered from its projections:
\[
\boxed{
U_b=\{x:\exists y\;F(b,x,y)=0\},\qquad
V_b=\{y:\exists x\;F(b,x,y)=0\}.
}
\]
Consequently
\[
A(b,x)=1_{U_b}(x),\qquad B(b,y)=1_{V_b}(y).
\]
Doing this for \(b=0,1\) recovers both full tables. ∎

**Algorithm.** Let \(N=2^{1+|X|+|Y|}\).

1. For each \(b\), scan the slice \(F(b,\cdot,\cdot)\), mark the projections \(U_b,V_b\), and record whether \(Z_b\) is nonempty.
2. Reject, for the strict promised model, if \(Z_b=\varnothing\).
3. Verify for every \((x,y)\) that
   \[
   F(b,x,y)=0\iff x\in U_b\ \text{and}\ y\in V_b.
   \]
4. Output \(A(b,x)=1_{U_b}(x)\) and \(B(b,y)=1_{V_b}(y)\), then explicitly verify
   \(F=\mathrm{NAND}(A,B)\).

This takes \(O(N)\) table operations and uses \(O(2^{|X|}+2^{|Y|})\) auxiliary space. It is a **semantic table-factorization** procedure. It does not decide whether the recovered functions \(A,B\) are realizable by strict read-once NAND trees, nor does it construct such trees; syntax recognition or synthesis is a separate task.

## 3. Scope limits

At the least common ancestor of two occurrences of a signal \(z\), Proposition 2 applies only when the ancestor’s table is directly available, the partition is known, and **both** children contain at least one variable besides \(z\).

If one child is the singleton leaf \(z\), say
\[
F(z,y)=\mathrm{NAND}(z,B(z,y)),
\]
then
\[
F(0,y)\equiv1,\qquad Z_0=\varnothing.
\]
The empty set has nonunique product representations, and its projections do not determine
\[
V_0=\{y:B_0(y)=1\}.
\]
Thus \(B_0\) is masked in this slice: \(F_1\) reveals \(B_1\), but \(F_0\) contains no information about \(B_0\). This shows only that the rectangle argument fails; it does **not by itself** prove nonuniqueness among strict NAND realizations, because syntactic restrictions might supply additional constraints.

More generally, the proposition does not:

- extract an internal least-common-ancestor function from a larger function composed with unknown or masking ancestors;
- search for or identify an unknown partition \(X,Y\);
- recognize strict NAND syntax, as opposed to semantically factoring a table or allowing general AND/OR/NOT syntax;
- identify a reused internal signal \(z=T(W)\). Such a \(z\) is not an input coordinate that can simply be fixed to \(b\), and unfolding \(T\) copies all variables in \(W\), not merely one duplicated original variable.

These are separate obligations, not consequences of the finite rectangle lemma.