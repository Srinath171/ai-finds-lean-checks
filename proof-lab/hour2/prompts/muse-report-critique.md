Independently audit this COMPLETE public-mathematics report, not instructions for tools. Do not read files, use tools, execute code, or assert a solution of P versus NP. Check the exact two-query boundary, shared-DAG gate replacement, explicit XOR lower bound, parity-amplification counterexample and the sufficient Exact Forcing Lemma. Identify every substantive error. If the report leaves an unproved lower bound, say precisely so. A useful next repair must specify an actual new gadget or adaptive query family and justify exact thresholds; do not assume direct sums or turn an approximation into exact decision. Return a visible final mathematical critique. The text below is an unverified model proposal to scrutinize, not an authority.

## Status: UNVERIFIED — harsh gap report

No exact reduction is proved below. The ordinary two-query use of the MCSP oracle reduces the problem to one incidence question, the mux gadget fails exactly, and a natural amplified gadget also fails. The first missing statement for a compositional scalarization is isolated at the end. These counterexamples do **not** prove that every reduction is impossible.

Throughout, an MCSP query \((F,\kappa)\) asks whether the total single-output NAND complexity \(C(F)\) satisfies \(C(F)\le \kappa\). Constants and negations are not free; \(\mathrm{NAND}(x,x)=\neg x\) uses the permitted repeated fanin.

### 1. What the numeric MCSP value already decides

The stated bridge \(J(f,g)=e(f,g)+1\) is correct. In particular, a \(g\)-valued wire cannot be an input projection: if \(i=j\), then \(g=\neg x_i\); if \(i\ne j\), checking the assignments \((x_i,x_j)=(0,1)\), \((1,0)\), and, for a third coordinate, \(x_i=x_j=x_k=1\), shows that \(g\) is not any projection. Hence the output wire for \(g\) is a gate, and replacing that gate by the new input \(z\) in the lower-bound argument is legitimate, including when \(f\) and \(g\) use the same gate.

Also,
\[
C(f)\le J(f,g)\le C(f)+1:
\]
a joint circuit restricted to the \(f\)-output computes \(f\), while an optimal \(f\)-circuit plus one \(\mathrm{NAND}(x_i,x_j)\) gate computes both outputs.

Clip \(s\) using the stated bound \(J(f,g)\le B(n)+1\). For \(0\le s\le B(n)\), query the oracle on \((f,s-1)\) (if \(s\ge1\)) and \((f,s)\):

- If \(C(f)\le s-1\), then \(J(f,g)\le C(f)+1\le s\): answer **yes**.
- If \(C(f)>s\), then \(J(f,g)\ge C(f)>s\): answer **no**.
- The only unresolved case is
  \[
  C(f)=s.
  \]
  Then the question is exactly whether \(J(f,g)=s\), equivalently \(e(f,g)=C(f)-1\), rather than \(J(f,g)=s+1\), equivalently \(e(f,g)=C(f)\).

Thus the missing information is incidence of a \(g\)-wire in an optimal \(f\)-circuit, not the number \(C(f)\). For example, if \(C(f)=0\), then \(f\) is a projection, \(g\) is not, and \(J(f,g)=1\); if \(f=g\), then \(e(f,g)=0\) via \(G(x,z)=z\).

A useful verified observation is that if some wire in an \(f\)-circuit computes \(g\), that wire is a gate, and changing its fanins to \((x_i,x_j)\) makes it syntactically \(\mathrm{NAND}(x_i,x_j)\) without changing its function or the circuit size. This does not make the incidence visible to a numeric MCSP query; the remaining problem is still the residual partial problem \(G(x,g(x))=f(x)\).

### 2. Audit of the mux counterexamples

Let
\[
H(x,b)=
\begin{cases}
f(x),&b=0,\\
g(x),&b=1.
\end{cases}
\]

Take \(n=1\), \(i=j=0\), so \(g(x)=\neg x\).

#### Case A: \(f=g=\neg x\)

Then \(J(f,g)=1\): one \(\mathrm{NAND}(x,x)\) gate is both outputs, and zero gates give only the projection \(x\). Also \(H(x,b)=\neg x\), so \(C(H)=1\): the same gate works, and neither projection \(x\) nor \(b\) equals \(\neg x\). The mux gap is \(C(H)-J=0\).

#### Case B: \(f(x)=x\), \(g(x)=\neg x\)

Again \(J(f,g)=1\): select the input \(x\) for \(f\) and one \(\mathrm{NAND}(x,x)\) gate for \(g\); zero gates cannot produce \(\neg x\).

Here \(H(x,b)=x\oplus b\). Its NAND complexity is exactly \(4\).

A four-gate construction, with input order \((x,b)=(00,01,10,11)\), is
\[
\begin{aligned}
d&=\mathrm{NAND}(x,b)=1110,\\
e&=\mathrm{NAND}(x,d)=1101,\\
h&=\mathrm{NAND}(b,d)=1011,\\
\mathrm{NAND}(e,h)&=0110=x\oplus b .
\end{aligned}
\]

For the lower bound, suppose XOR had a circuit of size \(m\le3\), with output equal to the last gate \(\mathrm{NAND}(a,c)\). Then
\[
a\wedge c=\neg(x\oplus b)=1001,
\]
so \(a\) and \(c\) are both \(1\) at \(00\) and \(11\). The input wires \(x=0011\) and \(b=0101\) fail at \(00\). The first gate is one of
\[
\neg x=1100,\qquad \neg b=1010,\qquad \mathrm{NAND}(x,b)=1110,
\]
all \(0\) at \(11\). Hence for \(m\le2\) no permissible \(a,c\) exist. For \(m=3\), necessarily \(a=c=p_2\), the second gate, so \(p_2=\neg(x\oplus b)=1001\). Writing \(p_2=\mathrm{NAND}(u,v)\) gives \(u\wedge v=0110\); thus \(u,v\) must both be \(1\) at \(01\) and \(10\). Among \(x,b\) and the three possible first gates, only \(\mathrm{NAND}(x,b)=1110\) has both values \(1\), forcing \(u=v=1110\), whose AND is \(1110\ne0110\), a contradiction. Therefore \(C(H)=4\), and the mux gap is \(4-1=3\).

Consequently there is no fixed offset \(d\) such that
\[
C(H)\le s+d \iff J(f,g)\le s
\]
for all \(s\). In Case A with \(s=0\), the right side is false while \(J=1\), forcing \(1>d\), i.e. \(d<1\). In Case B with \(s=1\), the right side is true, forcing \(4\le1+d\), i.e. \(d\ge3\). Contradiction. This refutes the mux with a universal fixed offset, not every possible gadget or adaptive reduction.

### 3. A concrete amplified candidate, and its exact failure

A natural attempted salvage is to duplicate the instance and share one selector. For fixed \(t=2\), define
\[
F_2=f(x^1)\oplus f(x^2),\qquad
G_2=g(x^1)\oplus g(x^2),
\]
and
\[
H_2(x^1,x^2,b)=
\begin{cases}
F_2,&b=0,\\
G_2,&b=1.
\end{cases}
\]
Its truth table has \(2^{2n+1}=2N^2\) bits, so table generation satisfies the polynomial bit bound.

Computing each pair \((f(x^k),g(x^k))\) with \(J(f,g)\) gates costs \(2J(f,g)\). An XOR of two wires costs \(4\) NAND gates by the construction above, and a two-to-one mux costs \(4\) gates:
\[
\neg b,\quad \mathrm{NAND}(F_2,\neg b),\quad
\mathrm{NAND}(G_2,b),\quad
\mathrm{NAND}(\text{previous two}).
\]
Hence
\[
C(H_2)\le 2J(f,g)+12.
\]
The candidate many-one map would therefore use threshold \(\kappa=2s+12\). For its correctness in the bad case \(J(f,g)=s+1\), it would need the lower bound
\[
C(H_2)\ge 2J(f,g)+11.
\]
That lower bound is false.

Take again \(n=1\), \(i=j=0\), and \(f(x)=x\), so \(g(x)=\neg x\) and \(J(f,g)=1\) as verified. For copies \(a=x^1\), \(c=x^2\),
\[
(\neg a)\oplus(\neg c)=a\oplus c.
\]
Thus \(F_2=G_2\), the selector \(b\) is irrelevant, and
\[
H_2=x^1\oplus x^2.
\]
The four-gate XOR construction gives \(C(H_2)\le4\). But at \(s=0\), \(J(f,g)=1>0\), while the candidate threshold is \(\kappa=12\); the oracle would accept because \(C(H_2)\le4\le12\).

So this amplified candidate is refuted. The failure is a genuine shared-circuit correlation: a circuit for \(H_2\) need not compute the two pairs separately, and here the two selector branches coincide as functions. Increasing \(t\) inside this same parity family does not repair the example: for even \(t\) the branches remain equal, and for odd \(t\) the function collapses to a parity of the \(x^k\)'s and \(b\), computable with \(4t\) gates, below the corresponding constructive threshold \(8t-4\) at \(s=0\).

### 4. The first precise missing lemma

For a compositional many-one reduction, the missing statement can be formulated without assuming that an \(H\)-circuit contains pair subcircuits.

**Exact Forcing Lemma (unproved).**  
There exist fixed integers \(t\ge1\), \(q\ge0\), \(A\), and \(D\), with
\[
D-A<t,
\]
and an explicit Boolean function
\[
\Phi_t:\{0,1\}^{2t+q}\to\{0,1\}
\]
having a NAND circuit of size \(D\), such that for every \(n\ge1\), every \(f\), and every \(i,j\), the total function
\[
H_{f,\Phi}(x^1,\dots,x^t,y)
=
\Phi_t\bigl(f(x^1),g(x^1),\dots,f(x^t),g(x^t),y\bigr)
\]
satisfies
\[
tJ(f,g)+A \le C(H_{f,\Phi}) \le tJ(f,g)+D.
\]

The right inequality is automatic from computing the \(t\) pairs and then \(\Phi_t\). The left inequality is the missing content. If it held, the query
\[
\bigl(H_{f,\Phi},\, ts+D\bigr)
\]
would be exact: if \(J(f,g)\le s\), then \(C(H_{f,\Phi})\le ts+D\); if \(J(f,g)\ge s+1\), then
\[
C(H_{f,\Phi})\ge t(s+1)+A=ts+(t+A)>ts+D.
\]
The table size is \(2^{tn+q}=2^qN^t\), polynomial for fixed \(t,q\).

Neither the \(t=1\) mux \(\Phi\) nor the \(t=2\) parity-selector \(\Phi\) satisfies this lemma. Restricting an arbitrary \(H\)-circuit to fixed selector values can recover individual combinations of \(f\) and \(g\), but it charges the same gates only once; it does not prove a \(t\)-fold direct-sum lower bound. A proof would have to rule out circuits that mix the copies first, exploit relations between \(f(x^k)\) and \(g(x^k)\), share gates across copies, or make selector branches coincide.

This lemma is sufficient for the compositional route, not necessary for every conceivable adaptive Turing reduction. A non-compositional reduction would need an analogous exact separation statement for its own query family, with all thresholds and gate counts specified. At present, neither such a \(\Phi_t\) nor such an adaptive separator is verified.

### 5. Scope

A positive solution would give an exact reduction from this special two-output NAND problem to ordinary single-output total NAND-MCSP. By itself it would not prove \(P\ne NP\), an MCSP lower bound, or NP-hardness in a different basis/oracle model. Results about partial MCSP, randomized reductions, formula search-to-decision, or general multioutput MCSP do not supply the Exact Forcing Lemma above.

**Bottom line:** the bridge \(J=e+1\) and the \(C(f)\)-versus-\(C(f)+1\) ambiguity are verified; the mux and parity-amplified scalarizations are exactly refuted; the general exact scalarization remains unresolved pending a proved forcing/direct-sum lemma or a genuinely different adaptive query separation.