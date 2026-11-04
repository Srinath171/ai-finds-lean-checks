## Verdict: **PASS**

The lemma is correct in the stated binary-NAND DAG model. The shorthand slot-counting argument needs the pruning/equality detail below, but there is no missing case or counterexample.

## Corrected proof

Let \(H=\operatorname{NAND}(f,g)\). Computing \(f\) in \(2\) gates, \(g\) in \(1\), and the final NAND in \(1\) gives \(C(H)\le 4\). We rule out \(C(H)\le 3\) when \(|\operatorname{supp}(f)\cup\operatorname{supp}(g)|>3\).

### 1. Slot-count normal form

Take a circuit for \(H\), delete every gate not ancestral to the output, and let \(k\) be the number of remaining gates. Every non-output gate occupies at least one later gate-input slot. Every semantically essential variable occupies at least one primary-input slot. Since there are \(2k\) input slots,
\[
2k\ge e+(k-1),\qquad\text{hence}\qquad k\ge e-1,
\]
where \(e\) is the number of essential variables of \(H\).

Thus \(e=5\) requires \(k\ge4\). If \(e=4\) and \(k\le3\), then necessarily \(k=3\) and equality holds throughout: exactly two slots are gate outputs, exactly four are distinct primary inputs, each non-output gate is used exactly once, each essential variable occurs exactly once, and there are no repeated leaves, \(\operatorname{NAND}(u,u)\) gate-inputs, extra variables, or unused gates. Hence the circuit is a read-once NAND formula tree.

A full binary tree with three NAND nodes has, up to order, only two shapes:

- balanced: leaf depths \((2,2,2,2)\);
- comb: leaf depths \((1,2,3,3)\).

NAND is antitone in each argument. A leaf at depth \(d\) is therefore weakly positive if \(d\) is even and weakly negative if \(d\) is odd. The possible strict polarity counts for four essential variables are therefore
\[
(+,+,+,+)\quad\text{or}\quad(-,+,-,-),
\]
i.e. \(4\) positive/\(0\) negative or \(1\) positive/\(3\) negative.

### 2. The \(C=2\) classification

In a minimal two-gate circuit, the first gate is \(u=\operatorname{NAND}(x,y)\), and the output must use \(u\).

- If the output is \(\operatorname{NAND}(u,u)\), it computes \(xy\); for complexity \(2\), \(x\ne y\), giving \(a\land b\).
- If the output is \(\operatorname{NAND}(u,w)\), it computes \(xy\lor\neg w\).
  - If \(x=y=a\), this is \(1\) when \(w=a\), otherwise an implication form \(\neg a\lor b\).
  - If \(x\ne y\), then \(w\in\{x,y\}\) again gives an implication form, while distinct \(w=c\) gives \(ab\lor\neg c\).

Thus, up to permutation, the \(C=2\) functions are
\[
1,\qquad a b,\qquad \neg a\lor b,\qquad ab\lor\neg c,
\]
with the displayed variables distinct in the nonconstant forms. The constant case has empty support, while \(g\) has support at most \(2\), so it cannot satisfy the hypothesis.

### 3. Exhaustive cases and obstructions

Since \(H=\neg f\lor\neg g\) and \(\neg\operatorname{NAND}(p,q)=pq\), the cases with support union \(>3\) are exactly:

1. **\(f=ab,\ g=\operatorname{NAND}(z,t)\), all distinct.**  
   \[
   H=\neg(ab)\lor zt.
   \]
   Polarities: \(a,b\) negative; \(z,t\) positive: \(2+/2-\).

2. **\(f=\neg a\lor b,\ g=\operatorname{NAND}(z,t)\), all distinct.**  
   \[
   H=(a\land\neg b)\lor zt.
   \]
   Polarities: \(3+/1-\).

3. **\(f=ab\lor\neg c,\ g=\operatorname{NAND}(a,z)\).**  
   \[
   H=(c\land\neg(ab))\lor az.
   \]
   Here \(a\) is non-unate: with \(b=c=1,z=0\), \(H=\neg a\); with \(c=0,z=1\), \(H=a\). A NAND tree is unate in every read-once leaf, so this is impossible.

4. **\(f=ab\lor\neg c,\ g=\operatorname{NAND}(c,z)\).**  
   \[
   H=c\land(\neg(ab)\lor z).
   \]
   Polarities: \(c,z\) positive; \(a,b\) negative: \(2+/2-\).

5. **\(f=ab\lor\neg c,\ g=\operatorname{NAND}(z,z)\).**  
   \[
   H=(c\land\neg(ab))\lor z.
   \]
   Polarities: \(2+/2-\).

6. **\(f=ab\lor\neg c,\ g=\operatorname{NAND}(z,t)\), all five distinct.**  
   \[
   H=(c\land\neg(ab))\lor zt,
   \]
   with five essential variables, already excluded by the slot count.

Essentiality is direct: for example, in Cases 4–6, \(a\) is isolated as \(\neg a\) by \(b=c=1,z=0\) (and \(t=0\) in Case 6), \(c\) is isolated in Case 4 by \(a=b=z=1\) and in Cases 5–6 by \(a=z=0\), and the remaining variables have analogous isolating assignments; Cases 1–3 are checked similarly. Cases 1, 2, 4, and 5 therefore have four essential variables but polarity patterns different from both tree patterns; Case 3 violates unateness; Case 6 has five essential variables.

Hence \(C(H)>3\), and with the generic four-gate construction,
\[
\boxed{C(\operatorname{NAND}(f,g))=4}.
\]

## Exact scope

The lemma unconditionally proves the \(>3\)-support case. Combined with a correct finite check of all \(\le3\)-input cases, it yields the intended universal \(C_2\) scalar-profile determinacy. That combined conclusion remains conditional on the finite record’s correctness—currently supported by audited Z3 UNSAT evidence and independently evaluated SAT witnesses, not a Lean-certified UNSAT proof.