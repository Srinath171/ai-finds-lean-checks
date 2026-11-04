## Status

**[UNRESOLVED: universal determinacy]** I do not exhibit a profile collision and do not prove that the labeled profile always determines \(J\). Below is a general arity-normal-form theorem, an exact \(c=2\) first-gate classification, and the precise remaining separation statement.

Here \(P(f,g)[h]=C(h(f,g))\), with \(h\) ranging over the sixteen labeled two-variable Boolean maps.

## 1. Arity normal form

Let \(g=\operatorname{NAND}(x_i,x_j)\), and let \(\operatorname{Ess}(f)\) be the set of variables on which \(f\) really depends.

### Theorem 1: Compression to \(c+3\) variables

If \(C(f)=c\), then \(|\operatorname{Ess}(f)|\le c+1\). Consequently, after deleting coordinates outside
\[
S=\operatorname{Ess}(f)\cup\{i,j\}
\]
and padding with dummy coordinates to exactly \(N=c+3\) variables, one obtains a pair \((f^*,g^*)\) such that:

1. \(g^*\) is again a NAND of two primary variables, repetition allowed;
2. \(C(f^*)=c\);
3. \(J(f^*,g^*)=J(f,g)\);
4. \(P(f^*,g^*)=P(f,g)\), componentwise for the labeled \(h\)'s.

Therefore a collision with different \(J\) exists somewhere iff one exists with both pairs on exactly \(c+3\) variables, where \(c\) is their common value of \(C(f)\).

### Proof

**Essential-variable bound.** Take a \(c\)-gate circuit for \(f\). If \(c=0\), then \(f\) is a primary variable, so \(|\operatorname{Ess}(f)|=1\). Suppose \(c\ge1\). The output cannot be a primary variable, since that would give \(C(f)=0\). Let \(A\) be the set of gates ancestral to the output gate, with \(m=|A|\le c\).

The \(m\) gates have \(2m\) input slots. Every non-output gate in \(A\) has a path to the output, and the first edge on such a path is a distinct slot sourced by that gate. Hence at least \(m-1\) slots are gate-sourced, so at most \(2m-(m-1)=m+1\) slots are primary-sourced. Every essential variable must occur in one of those primary slots. Thus
\[
|\operatorname{Ess}(f)|\le m+1\le c+1.
\]
Therefore \(|S|\le c+3\).

**Deleting unused coordinates.** Write \(S=\{s_1<\cdots<s_m\}\). Since \(i\in S\), \(m\ge1\). Define \(F\) on \(y_1,\dots,y_m\) by restricting \(f\) to the coordinates in \(S\); the values outside \(S\) are irrelevant because \(\operatorname{Ess}(f)\subseteq S\). Similarly, \(G\) is the corresponding NAND in the \(y\)-coordinates.

Given a circuit over the \(x\)'s, replace each leaf \(x_{s_t}\) by \(y_t\), and replace each leaf outside \(S\) by the existing primary wire \(y_1\). Gate count and gate structure are unchanged. Evaluated at \(y\), the transformed circuit equals the original circuit at the extension whose outside-\(S\) coordinates all equal \(y_1\). Hence, for every function depending only on \(S\)—in particular \(f\), \(g\), the pair \((f,g)\), and every \(h(f,g)\)—the transformed circuit computes the corresponding restricted function. This uses only rewiring to an existing primary input, not a free constant or complement.

Conversely, a circuit over the \(y\)'s lifts to the \(x\)'s by sending \(y_t\) to \(x_{s_t}\). These two transformations preserve gate count exactly. Output selectors cause no exception: a selector equal to an outside primary would make the selected function depend on that outside coordinate. Applying this to single-output circuits gives preservation of \(C\) for \(f\) and for every \(h(f,g)\); applying it to two-output circuits gives preservation of \(J\).

**Padding.** Padding is the inverse operation: embed the \(m\) coordinates into \(N\ge m\) coordinates and ignore the remaining ones. The same deletion argument shows that all scalar costs and the joint cost are preserved. Take \(N=c+3\).

Finally, if \(P(f,g)=P(f_2,g_2)\) but \(J(f,g)\ne J(f_2,g_2)\), then the entry \(h(a,b)=a\) shows that the two pairs have the same \(c=C(f)\). Normalizing both to \(N=c+3\) preserves profiles and \(J\)'s, yielding a normalized collision. The converse is immediate. ∎

### Consequence

For each **fixed** \(c\), determinacy is a finite question about pairs on \(c+3\) variables. This is not a uniform decision procedure over all \(c\), and the finite search space is enormous in general.

In particular, the audited \(n=3\) evidence does not settle \(c=2\): Theorem 1 gives arity \(5\), so pairs whose combined essential support has size \(4\) or \(5\) are outside that evidence.

## 2. The proved lower-bound test and its gap

Let \(\mu(h)\) be the NAND cost of \(h(a,b)\) when \(a,b\) are free input signals. If a joint circuit computes \((f,g)\) with \(J\) gates, replacing the two free arguments in a \(\mu(h)\)-gate circuit for \(h\) by the signals \(f,g\) computes \(h(f,g)\) with at most \(J+\mu(h)\) gates. Hence
\[
C(h(f,g))\le J+\mu(h),
\qquad
L:=\max_h\bigl(P(f,g)[h]-\mu(h)\bigr)\le J.
\]
Since \(c\le J\le c+1\), if \(L=c+1\), then \(J=c+1\).

**[UNRESOLVED: separation in the case \(L\le c\)]** When \(L\le c\), this argument gives no conclusion. The exact missing statement is:

> For every \(c\ge2\), every profile arising on \(c+3\) variables is \(J\)-homogeneous: it cannot arise both from a pair with \(J=c\) and from a pair with \(J=c+1\).

Equivalently, one must either prove that every such profile fiber has one \(J\)-value, or exhibit two normalized pairs in one fiber with different \(J\).

## 3. Exact first-gate structure at \(c=2\)

The following classification sharpens the remaining \(c=2\) problem.

### Theorem 2

Up to permuting input variables, a function \(f\) with \(C(f)=2\) is one of
\[
1,\qquad x_1\wedge x_2,\qquad \neg x_1\vee x_2,\qquad
(x_1\wedge x_2)\vee\neg x_3
\]
with distinct displayed variables in the last three forms. Moreover, for \(g=\operatorname{NAND}(x_i,x_j)\):

- if \(f=1\), then \(J(f,g)=2\) iff \(g=\neg x_t\) for some \(t\);
- if \(f=x_1\wedge x_2\), then \(J(f,g)=2\) iff \(g=\operatorname{NAND}(x_1,x_2)\);
- if \(f=\neg x_1\vee x_2\), then \(J(f,g)=2\) iff
  \[
  g=\operatorname{NAND}(x_2,x_2)=\neg x_2
  \quad\text{or}\quad
  g=\operatorname{NAND}(x_1,x_2);
  \]
- if \(f=(x_1\wedge x_2)\vee\neg x_3\), then \(J(f,g)=2\) iff \(g=\operatorname{NAND}(x_1,x_2)\).

Otherwise \(J(f,g)=3\).

### Proof

Take a two-gate circuit for \(f\), with first gate \(\alpha=\operatorname{NAND}(u,v)\). The output gate must use \(\alpha\); otherwise \(C(f)\le1\).

If the output is \(\operatorname{NAND}(\alpha,\alpha)=\neg\alpha\), then \(f=u\wedge v\). The case \(u=v\) gives a variable, contradicting \(C(f)=2\); hence \(u,v\) are distinct and \(f\) is an AND of two variables.

If the output is \(\operatorname{NAND}(\alpha,w)\) for a primary \(w\), then
\[
f=\neg(\neg(u\wedge v)\wedge w)=(u\wedge v)\vee\neg w.
\]
If \(u=v\), this is \(u\vee\neg w\): constant \(1\) when \(w=u\), otherwise an implication form. If \(u\ne v\), then \(w\) distinct gives the three-variable form, while \(w=u\) gives
\[
(u\wedge v)\vee\neg u=\neg u\vee v,
\]
and similarly for \(w=v\). This proves the classification.

Now suppose \(J(f,g)=2\). In a two-gate joint circuit, the gates ancestral to \(f\) must number at least \(C(f)=2\), hence both gates; so the circuit is an \(f\)-circuit and \(g\), not being equal to \(f\), is its first gate. Conversely, if some two-gate \(f\)-circuit has first gate \(g\), then \(J(f,g)=2\).

It remains to list possible first gates. In the \(\neg\alpha\) output case, \(\alpha=\neg f\). This is a primary NAND exactly for \(f=x_1\wedge x_2\), where \(\alpha=\operatorname{NAND}(x_1,x_2)\). For \(f=\neg x_1\vee x_2\), \(\neg f=x_1\wedge\neg x_2\) has two essential variables but is not symmetric in them, so it is neither \(\neg x_t\) nor \(\operatorname{NAND}\) of two distinct primaries. For the three-variable form, \(\neg f\) has three essential variables; for \(f=1\), \(\neg f=0\) is not a NAND of primaries.

In the \(\operatorname{NAND}(\alpha,w)\) case, compare the formulas above with the four canonical \(f\)'s. AND is distinguished from implication by having one satisfying assignment on its two essential variables rather than three, and from the three-variable form by essential count. Implication forces either \(\alpha=\neg x_2\) in the \(u=v\) subcase, or \(\alpha=\operatorname{NAND}(x_1,x_2)\) in the \(u\ne v\), \(w\in\{u,v\}\) subcases. The three-variable form forces \(\alpha=\operatorname{NAND}(x_1,x_2)\). For \(f=1\), the \(u=v\) subcase gives \(1\) exactly when \(w=u\), forcing \(\alpha=\neg u\); the \(u\ne v\) subcase never gives \(1\), as shown by choosing assignments: if \(w\) is distinct take \(w=1,u=0\); if \(w=u\) take \(u=1,v=0\); if \(w=v\) take \(v=1,u=0\). ∎

### What remains at \(c=2\)

Relative to the canonical forms in Theorem 2, a pair is determined by the roles occupied by \(i,j\): core variables, the negative variable, or outside variables, including equality of the two outside variables. If
\[
|\operatorname{Ess}(f)\cup\{i,j\}|\le3,
\]
the pair is represented in the audited \(n=3\) evidence. The canonical \(c=2\) categories with combined support \(4\) or \(5\), all with \(J=3\) by Theorem 2, are exactly:

1. \(f=x_1\wedge x_2\), \(g=\operatorname{NAND}(z,t)\) with \(z,t\) distinct outside variables;
2. \(f=\neg x_1\vee x_2\), \(g=\operatorname{NAND}(z,t)\) with \(z,t\) distinct outside variables;
3. \(f=(x_1\wedge x_2)\vee\neg x_3\), with \(g\) of one of the types
   \[
   \operatorname{NAND}(x_1,z),\quad
   \operatorname{NAND}(x_3,z),\quad
   \operatorname{NAND}(z,z),\quad
   \operatorname{NAND}(z,t),
   \]
   where \(z,t\) are outside variables, distinct in the last type.

**[UNRESOLVED: formal \(c=2\) closure]** One must compute, with proof-grade verification, the exact profiles of these six categories and compare them with the profiles of all \(c=2\) categories of support at most \(3\). The existing \(n=3\) computation is strong finite evidence for the latter, but its UNSAT results are not here treated as formally certified mathematical proof.

## 4. Uniqueness versus an effective decoder

Uniqueness and a polynomial-time decoder are different assertions.

- If uniqueness holds, an abstract decoder \(D\) from realized profiles to \(J\) exists by choosing any representative of a profile.
- Theorem 1 even makes brute-force decoding computable in principle: read \(c\) from the projection entry, enumerate pairs on \(c+3\) variables, compute exact profiles and \(J\)'s by increasing-size circuit search, and output the \(J\) of a matching pair. NAND gives \(\neg s=\operatorname{NAND}(s,s)\) and \(s\wedge t=\neg\operatorname{NAND}(s,t)\), so finite truth tables have finite NAND circuits and the search terminates on realized profiles. But the number of truth tables is double-exponential in \(c+3\); this gives no decoder polynomial in \(c\).

**[UNRESOLVED: polynomial-in-\(c\) decoder]** A positive answer in the strong sense would require an explicit rule computing \(J\) from the sixteen profile integers in time polynomial in \(c\).

Even that would **not** prove \(P=NP\): it would only reduce the narrow joint question to sixteen ordinary scalar circuit-size values \(C(h(f,g))\). Computing those values from truth tables is still the ordinary circuit-minimization problem. Conversely, a collision would show only that these particular sixteen scalar summaries lose the relevant gate-sharing information; it would not rule out other queries or summaries, and would not separate complexity classes.