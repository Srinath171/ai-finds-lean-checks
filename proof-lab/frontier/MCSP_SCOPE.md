# Truth-table circuit bounds and the scope of MCSP

`MCSPScope.lean` turns the finite-sample interpolation theorem into a
universal circuit bound. This is a general theorem for every positive
input arity, not a test on a small fixed number of variables.

## Checked claims

`allAssignments n` contains every Boolean list of length `n`, exactly once.
Its membership characterization, absence of duplicates, and exact length
`2^n` are formal theorems.

Define

```text
B(n) = 3 + (3*n+7)*2^n.
```

`universal_circuit_bound` proves: for every `n>=1` and every target
`f : List Bool -> Bool`, there is an independently well-formed NAND circuit
with at most `B(n)` gates whose output equals `f a` for every assignment
list `a` of length `n`. The claim places no restriction on `f` at lists of
other lengths. It follows by applying
`exists_circuit_agreeing_on_assignments` to the complete assignment list;
all constants and literal negations in that compiler use paid NAND gates.

`HasCircuit n f k` explicitly includes the independent
`WellFormedCircuitN` predicate, the gate-count limit, and pointwise semantic
agreement on every valid `n`-bit assignment. Thus neither enumeration
membership nor an out-of-range default is substituted for well-formedness.

`bounded_witness` and `threshold_clipping` prove

```text
HasCircuit n f k <-> HasCircuit n f (min k B(n)).
```

If `k<=B(n)`, retain the assumed witness. Otherwise, use the universal
construction. Also, `threshold_above_bound_yes` proves every target has a
circuit under any threshold `k>=B(n)`. The degenerate arity `n=0` is
excluded because this NAND model has no free constants or initial signals.

## Mathematical verification argument; not a formal class theorem

For truth-table MCSP, distinguish the arity `n` from the truth-table length
`N=2^n`. The input consists of the `N` output bits (in the fixed assignment
order) together with a binary threshold `k`, using approximately
`N+log(k+1)` bits, plus ordinary framing information.

The formal threshold theorem permits a yes-instance witness to use at most
`B(n)=3+(3*n+7)*N=O(N*log N)` NAND gates even if `k` has an enormous binary
value. A topological circuit description stores two earlier wire indices
per gate and one output index. Its length is

```text
O((B(n)+1) * log(n+B(n)+1)) = O(N * (log N)^2)
```

bits, up to the usual framing/length fields. The witness is therefore
polynomial in the truth-table input size, independent of the numeric value
of a potentially large `k`.

A verifier checks every fanin/output bound and the gate count, then evaluates
the circuit on all `N` assignments and compares all output bits with the
input table. This takes `O(N*(B(n)+n))`, conventionally `O(N*B(n))` here,
in a unit-cost indexed Boolean evaluation model; accounting for address
bit operations still gives a polynomial bound. Comparing the witness size
with the binary threshold is also polynomial in its bit length.

This is the ordinary mathematical NP-verification argument for the stated
truth-table NAND-circuit decision problem. **Turing machines, binary
encodings, time bounds, and complexity classes are not defined or proved
in this Lean file.** In particular, the formal threshold theorem itself is
about natural-number thresholds, not a proved binary-encoding reduction.

## What does not follow

Counting establishes that some Boolean functions require large circuits.
MCSP asks how difficult it is to decide circuit-size bounds when the whole
truth table is supplied. A circuit-size lower bound for a function is not
a running-time lower bound for this different decision problem. The
exponential dependence on `n` above is polynomial in `N`, which is the
relevant input length for truth-table MCSP.

Nothing here establishes MCSP NP-hardness, a superpolynomial lower bound
for deciding MCSP, NP membership of a succinct truth-table variant, or a
P versus NP separation.

## Verification

Compiled using installed Lean 4.35.0 with project `LEAN_PATH`:

```powershell
$env:LEAN_PATH = (Get-Location).Path
& C:\Users\email\.elan\bin\lean.exe frontier\MCSPScope.lean
```

Exit code 0, no warnings. Printed axioms for enumeration coverage/count,
the universal circuit theorem, and clipping contain only `propext`,
`Classical.choice`, and `Quot.sound`. No placeholders, new axioms,
`native_decide`, or proof-time IO shortcuts are used.