# First-gate deletion gives a partial extension, not a total MCSP query

`FirstGateExtension.lean` verifies the exact general deletion/prefixing
identity for the project's shared, topologically ordered NAND circuit model.
The circuit predicates include independent fanin and output-selector
well-formedness; free constants and complemented inputs are not added.

## Formal equivalence

For an `n`-bit assignment list `a`, define

```text
graphInput(a,i,j) = a ++ [NAND(a_i,a_j)].
```

For every `n>=1`, `s>=1`, and target `f`,
`first_gate_extension_iff` proves

```text
HasCircuit(n,f,s)
  iff there exist i,j<n and an independently well-formed G on n+1 inputs,
      gates(G)<=s-1,
      G(graphInput(a,i,j))=f(a) for EVERY assignment a of length n.
```

Deleting a nonempty circuit's first gate reinterprets its output wire as
one extra free input. That wire has index `n` in both descriptions; a later
gate formerly at index `n+1+k` keeps that same index. All remaining fanin
and output indices stay unchanged. Conversely, prefixing the paid NAND
gate reconstructs the original semantics and increases the gate count by
one. The proof allows repeated fanins, unlimited sharing, unused gates,
outputs selecting inputs, and outputs selecting the first gate.

An original circuit may use zero gates even though the allowed threshold
is positive. In that case it is a projection. The forward proof chooses
`i=j=0` and keeps the same zero-gate projection as G; it ignores the extra
input. The assumptions `n>=1` and `s>=1` make that case valid.

## Total function versus fixed total truth table

`circuitFunction` defines a total pointwise Boolean evaluator for G.
`first_gate_total_completion_iff` additionally states the equivalence as

```text
HasCircuit(n,f,s)
  iff there exist i,j<n and a total function g,
      HasCircuit(n+1,g,s-1),
      g(graphInput(a,i,j))=f(a) for every valid n-bit a.
```

The completion `g` is existential. Only its values on the graph are
constrained; values on the other rows can be chosen to make a small circuit
possible. This is not the same as supplying a predetermined total truth
table to a standard MCSP decision oracle. The Lean theorem does not
construct such an oracle reduction.

## Checked failure of zero filling

Take `n=1`, `s=1`, `f(x)=x`, and first gate `NAND(x,x)=NOT x`.
The partial graph is `z=NOT x`. The total function `g(x,z)=x` is a
zero-gate extension, selecting the original input and ignoring z.

If every unspecified row is instead set to false, the completed function
is `h(x,z)=x AND NOT z`:

| x | z | On graph z=NOT x? | Zero-filled h |
|---|---|---|---|
| false | false | No | false |
| false | true | Yes | false |
| true | false | Yes | true |
| true | true | No | false |

`zeroFill_is_zero_completion` checks the precise fill rule, and
`zeroFill_agrees_on_graph` checks agreement with f. Nevertheless,
`zeroFill_no_zero_gate_circuit` proves h has no well-formed zero-gate
2-input circuit: such a circuit must be one of the two projections, and
both return true at `(true,true)`, where h returns false.
`zero_fill_counterexample` combines the original yes-instance, valid
residual extension, graph agreement, and zero-fill failure.

## Nonprojection strengthening: two-input AND

The file also verifies a counterexample that survives a projection-base-case
check. Let `f(x,y)=x AND y`, `n=2`, and `s=2`. The explicit original circuit
is `[(0,1),(2,2)]`, output 3: first compute `z=NAND(x,y)`, then `NOT z`.
`and2_within_two` verifies its independent well-formedness, two-gate budget,
and agreement on every two-bit assignment. `and2_not_projection` separately
proves that f has no zero-gate circuit.

After deleting the first gate, `[(2,2)]`, output 3, is a legal one-gate
circuit on three inputs `(x,y,z)`. Its total function is `NOT z`, and
`and2_residual_extension` verifies agreement with f on the full graph
`z=NAND(x,y)`.

Zero filling the other four rows instead produces

```text
h(x,y,z) = x AND y AND NOT z.
```

`zeroFillAND_is_zero_completion` checks that exact fill rule, and
`zeroFillAND_agrees_on_graph` checks graph agreement. The file explicitly
exhibits each of h's three essential input variables. By the independently
proved general dependency theorem, any well-formed NAND circuit with at
most one gate depends on at most two inputs. Thus
`zeroFillAND_no_one_gate_circuit` proves that this filled total function
has no circuit within the residual one-gate budget. No finite circuit
search or unchecked dependency assumption is used.

`nonprojection_zero_fill_counterexample` combines the original yes-instance,
its nonprojection property, the valid residual partial extension, agreement
of the zero completion on the graph, and failure of its total one-gate
MCSP instance. No exact minimum circuit size for h is claimed.

## All four candidate first pairs fail under zero filling

`and2ZeroCompletion i j` preserves AND2 on the graph of the proposed
first NAND of input positions i and j, and sets all other rows to false.
`and2ZeroCompletion_eq_zeroFillAND` proves, for every `i,j<2`, that this
completion equals the same `x AND y AND NOT z` function. The reason is
that AND2 is true only at `(true,true)`, where every candidate NAND is
false, including repeated fanins.

`every_first_pair_zero_fill_fails` therefore proves that all four completed
three-input functions have no circuit within the residual one-gate budget.
`all_first_pairs_zero_fill_counterexample` combines:

- the original two-input AND circuit has at most two gates;
- the original target is not a projection;
- a valid one-gate partial graph extension exists; and
- no candidate first pair produces a zero-filled total truth table with
  a circuit of at most one gate.

Thus OR-ing the four same-residual-threshold zero-filled MCSP answers
still returns no on this original yes-instance. The refutation applies to
that concrete one-step algorithm, even with a projection-base-case check;
it is not a refutation of arbitrary fillings, threshold calibrations,
multi-query reductions, or all circuit-search approaches.

This refutes that particular zero-fill oracle substitution. It does not
refute all polynomial reductions, all self-reducibility approaches, or
any complexity-class equality. No MCSP hardness or P versus NP conclusion
is proved.

## Verification

Compiled with installed Lean 4.35.0 and project `LEAN_PATH`:

```powershell
$env:LEAN_PATH = (Get-Location).Path
& C:\Users\email\.elan\bin\lean.exe frontier\FirstGateExtension.lean
```

Exit code 0, no warnings. Printed axioms for both general equivalences,
the exact zero-completion rule, and the combined counterexamples contain
only `propext`, `Classical.choice`, and `Quot.sound`. No placeholders, new
axioms, `native_decide`, or proof-time IO shortcuts are used.