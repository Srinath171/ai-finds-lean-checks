# A fixed computable family with an explicit exponential threshold

## Statement and circuit model

For every integer `n >= 16`, put

\[
k=\lfloor n/4\rfloor,\qquad s(n)=2^k.
\]

Then the proposed inequality is **true**:

\[
\boxed{(s+1)(n+s)^{2s+1}<2^{2^n}.}
\]

Here circuits have `n` input variables, binary NAND gates, arbitrary fanout,
ordered gate inputs with repetition permitted, and an output chosen from
any input or gate output. There are no free constants or complemented
inputs. Size means the number of NAND gates. A topological gate list is
used to describe each circuit. The proof below is elementary mathematics;
the inequality and the resulting existential hard-function bound are now formalized in [ExplicitSchedule.lean](ExplicitSchedule.lean); see [the precise formal scope](EXPLICIT_SCHEDULE_FORMAL.md). The lex-first selector and its computation analysis below remain separate mathematical arguments.

## An all-n proof, including n = 16, 17, 18, 19

For every integer `k >= 4`,

\[
4k+3\le 2^{k+1},\qquad k+2\le 2^k.
\tag{1}
\]

Both follow by induction. At `k = 4` they read `19 <= 32` and `6 <= 16`.
For the first induction step,

\[
4(k+1)+3=4k+7\le 2(4k+3)\le 2^{k+2}.
\]

For the second,

\[
(k+1)+2=k+3\le 2(k+2)\le 2^{k+1}.
\]

Since `4k <= n <= 4k+3`, (1) gives

\[
n\le 2s,\qquad k+2\le s.
\]

Consequently

\[
s+1<2s=2^{k+1},\qquad n+s\le 3s<4s=2^{k+2}.
\]

Let `B = (s+1)(n+s)^(2s+1)`. Taking base-two logarithms,

\[
\begin{aligned}
\log_2 B
&< (k+1)+(2s+1)(k+2)\\
&\le s+(2s+1)s\\
&=2s^2+2s\\
&\le 3s^2\\
&<s^4\\
&=2^{4k}\\
&\le 2^n.
\end{aligned}
\]

The penultimate strict inequality uses `s >= 16`, so `s^2 > 3`.
Exponentiating proves the boxed inequality. Notice that the proof uses
`n <= 2s`, not `n <= s`: the latter fails at `n = 17, 18, 19`.

For all four boundary values `n = 16..19`, the first line is already
`log2(B) < 5 + 33*6 = 203`, whereas `2^n >= 65536`.

## Why a missing table exists

The exact number of topological descriptions with exactly `j` gates is

\[
D_j(n)=(n+j)\prod_{i=0}^{j-1}(n+i)^2.
\]

The empty product is one; thus `D_0(n) = n`, accounting for each input
as an output. For each `0 <= j <= s`,

\[
D_j(n)\le(n+s)^{2j+1}\le(n+s)^{2s+1}.
\]

Therefore the number of descriptions of size at most `s` satisfies

\[
D(n,s)=\sum_{j=0}^{s}D_j(n)
\le(s+1)(n+s)^{2s+1}
<2^{2^n}.
\]

Every circuit in the stated model has such a topological description.
Different descriptions can compute the same function, which only
strengthens the upper bound on the number of computed truth tables.
There are exactly `2^(2^n)` Boolean truth tables on `n` inputs, so at
least one table is not computed at size at most `s(n)`.

## One family, rather than a family that depends on a chosen polynomial

For every `n >= 16`, define `f_n` to be the lexicographically first
missing truth table for this particular threshold `s(n)`. The order is
assignment zero first: compare the output tuples
`(b_0, b_1, ..., b_(2^n-1))`. For `0 <= n < 16`, set `f_n` identically
zero. These rules specify **one fixed family** `(f_n)`.

By construction, for every `n >= 16`,

\[
\operatorname{NANDsize}(f_n)>2^{\lfloor n/4\rfloor}.
\]

In particular,

\[
2^{\lfloor n/4\rfloor}\ge 2^{-3/4}2^{n/4},
\]

so the circuit lower bound is exponential in `n`, not merely a lower
bound against one fixed degree of polynomial. Every polynomial threshold
is eventually smaller than this single prescribed schedule.

The family is uniformly computable. A terminating algorithm, given `n`,
enumerates every description up to the threshold, evaluates its truth
table, and selects the first missing table. On an input string `x`,
it returns the appropriate bit of `f_|x|`; use assignment index
`sum(x_i * 2^i)` to match the circuit convention. This defines a single
decidable language.

The bound is stated exactly for the NAND model. It also implies an
exponential lower bound for any fixed finite Boolean basis of bounded
fan-in: each such gate has a constant-size NAND implementation. Allowing
free constants does not change this asymptotic conclusion, because both
constants can be generated using three NAND gates from an input when
`n >= 1`. These conversions change only fixed factors and additive
constants. No claim is made for a model in which an arbitrary Boolean
function or an unbounded-fan-in operation is a unit-cost primitive.

## Computation cost: a double exponential enumeration, not an NP algorithm

The sharper bound before replacing `k+2` by `s` is

\[
\log_2 D(n,s)
< (k+1)+(2s+1)(k+2)
=O\!\left(n2^{n/4}\right).
\]

A direct algorithm can enumerate `D` descriptions and evaluate each on
all `2^n` assignments. Evaluation and description bookkeeping cost only
a polynomial factor in `n`, `s`, and `2^n` per description. Store the
computed truth tables as lexicographic ranks, sort them, discard
duplicates, and take their mex. Each rank has `2^n` bits, and there are
at most `D` ranks. Sorting needs `O(D log D)` comparisons, each using at
most `O(2^n)` bit comparisons. The mex scan inspects at most `D+1` ranks;
it does not scan all `2^(2^n)` possible tables.

This gives a deterministic time upper bound, in an ordinary bit model,

\[
2^{O(n2^{n/4})},\qquad\text{and hence also}\qquad 2^{2^{O(n)}}.
\]

This is a double exponential upper bound in input length `n`. The bound
is neither polynomial nor singly exponential `2^(poly(n))`; no lower
bound on every possible algorithm for this language is inferred from it.
A straightforward stored-table implementation also uses enormous space;
no efficiency claim follows from termination or from the fact that the
construction is specified explicitly.

There is **no NP-membership argument here**. The construction does not
provide polynomial-length witnesses with a polynomial-time verifier for
membership in this particular language. This note neither proves nor
refutes that the family is in NP; asserting that it is would add a
substantial unsupported premise. A computable language with exponential
circuit lower bounds, without a small complexity-class membership result,
is not a P vs NP separation.

## Exact finite arithmetic check (supporting evidence, not the all-n proof)

Using Python integers, all 49 cases `n = 16..64` passed the following
check. It never constructs the infeasibly large integer `2^(2^n)`:

```python
for n in range(16, 65):
    k = n // 4
    s = 1 << k
    B = (s + 1) * pow(n + s, 2*s + 1)
    assert B.bit_length() <= (1 << n)
```

For a positive integer `B`, `B.bit_length() <= E` is exactly equivalent
to `B < 2^E`. Thus the test uses exact integer arithmetic, with no
floating-point logarithms or rounding assumptions.

| n | k | s | B.bit_length() | 2^n |
|---:|---:|---:|---:|---:|
| 16 | 4 | 16 | 170 | 65536 |
| 17 | 4 | 16 | 171 | 131072 |
| 18 | 4 | 16 | 172 | 262144 |
| 19 | 4 | 16 | 174 | 524288 |
| 20 | 5 | 32 | 376 | 1048576 |
| 32 | 8 | 256 | 4200 | 4294967296 |
| 48 | 12 | 4096 | 98466 | 281474976710656 |
| 64 | 16 | 65536 | 2097369 | 18446744073709551616 |

The induction and inequality chain establish every `n >= 16`; these
finite computations check boundary arithmetic and implementation only.
