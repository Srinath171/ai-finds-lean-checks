# Independent review of the first-gate follow-up

Reviewed only the public `visible_text` in
`background-first-gate/state.json` and `text` in its `claude-audit.json`.
No live model calls or external literature checks were made. **The new
research claims remain UNVERIFIED as formal results**, except for the
specific existing Lean theorems identified below. This is a mathematical
review, not a P versus NP result or a novelty certification.

## Quantitative claims

The ignore-fill inequalities are correct for n>=1:

```text
e_j <= C(I_j) = C(f) <= e_j+j.
```

An extension plus the j prefix gates computes f. Conversely, a circuit for
f can ignore the extra inputs. To justify the equality despite possible
use of extra inputs inside a circuit computing I_j, replace every extra
primary input by an original input, such as x_0, and renumber later gates.
Because I_j ignores those inputs, the resulting circuit still computes f,
without increasing its gate count. No free constant is needed.

The zero-fill bound `e_j <= C(Z_j) <= e_j+8j` is also correct as an
unformalized construction. Recompute the j prefix gates, use five NANDs
per XNOR comparison, then two NANDs per AND with the existing output:
`j+5j+2j=8j`. The stated XNOR formula is correct. These bounds provide an
interval, not an exact decision at either endpoint. Their general circuit
syntax, size, and dense-table writing costs have not been formalized here.

The dense-table caveat is material: a table on n+j variables contains
`2^(n+j)` bits. An output polynomial in `N=2^n` and threshold bit length
cannot generally write that table for a long prefix. This says nothing by
itself against a different succinct encoding or multi-query reduction.

Claude's objection that `B(n)=Theta(nN)` lacks support is inapplicable to
this project's stated cap: `MCSPScope.lean` already proves the explicit
upper bound `B(n)=3+(3n+7)2^n`. This cap need not be an optimal universal
bound. The audit's external literature claims were not independently
checked and are not used in this review.

## Counterexamples

The ignore-fill AND example with prefix NOT x is correct. On graph rows
00,01,10,11, the target is 0001; the three projections are 0011,0101,1100;
the six symmetric one-NAND choices give
1100,1110,1111,1010,1011,0011. None matches. AND itself has a two-NAND
circuit, so the shifted necessary test is not sufficient.

The same-threshold zero-fill AND example is now formally covered by
`FirstGateExtension.nonprojection_zero_fill_counterexample`. Its zero
completion has three essential variables, so the independently checked
s+1 dependency bound excludes a one-gate circuit.

The stronger `all_first_pairs_zero_fill_counterexample` is also Lean
checked: for every i,j<2, zero filling AND2 on that NAND graph yields the
same x AND y AND NOT z function. All four residual budget-1 total MCSP
queries are no, although the original budget-2 instance is yes and not a
projection. Thus even OR-ing all first-pair zero-fill queries fails at
this unchanged residual threshold.

The XOR shifted-threshold example is mathematically correct but not yet
Lean formalized here. None of the three projections or six one-NAND
restrictions on z=NAND(x,y) gives 0110. Its zero fill is `(x XOR y) AND z`,
with the explicit six-gate circuit

```text
[(0,1),(0,3),(1,3),(4,5),(6,2),(7,7)], output 8
```

on three inputs. Hence the budget-9 shifted query is yes while the
residual budget-1 partial instance is no. An independent local Boolean
calculation checked these restriction lists and all eight rows of the
six-gate implementation; this calculation is not a Lean proof.

## Fixed pointwise-fill obstruction: correct with limited scope

For a single fixed rule Phi satisfying Phi(a,b,b)=a, write
psi(a,b)=Phi(a,b,1-b). Fix prefix p=NAND(x,y).
If psi(1,1)=0, choose f=x. The three displayed assignments distinguish its
filled function from each zero-gate projection. If psi(1,1)=1, choose f=p:
the filled function is true at (0,0,0), where every projection is false.
Each partial instance has a zero-gate extension. Thus no such universal
fixed pointwise rule preserves the exact minimum, or the unshifted
same-threshold answer, on every instance. An independent local calculation
also checked all 16 possible off-graph rules.

This does not rule out instance-dependent/global fill choices, shifted or
recalibrated thresholds, or more general reductions. The completion rule
must be the same across the adversarial targets, and depends only on
(f(x,y),p(x,y),z).

One statement in Claude's audit is false: these filled counterexamples do
NOT always have circuit size at most one. For the all-zero off-graph rule
and f=x, the filled function is `x AND (y XOR z)`, with three essential
variables, hence no circuit of at most one gate. This error does not harm
Muse's original obstruction proof, nor does it establish a universal
obstruction to threshold recalibration.

## Suggested next formal lemma; not implemented

A compact worthwhile lemma would quantify over all
`Phi : Bool -> Bool -> Bool -> Bool` with `Phi a b b=a`, and produce one of
the two targets f=x or f=NAND(x,y) such that a zero-gate partial extension
exists but its Phi-filled three-input function has no zero-gate circuit.
The proof splits on `Phi true true false` and uses the explicit projection
witnesses above. This would formalize only the fixed-rule same-threshold
obstruction, not a theorem excluding all total-MCSP reductions.

SEC-1 and its compressed long-prefix counterpart are not constructed by
these arguments. They should be described as missing from this approach,
without asserting an externally established open-problem classification.
Even a successful search-to-total-MCSP reduction would not itself settle
P versus NP.