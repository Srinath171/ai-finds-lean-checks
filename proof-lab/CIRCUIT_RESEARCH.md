# Circuit Lab Research Note: Exact Finite NAND Bounds

## Scope (precise)

This note records **exact, finite** results about tiny NAND circuits in
one fixed model. It makes **no** asymptotic claim. In particular, nothing
here is a superpolynomial lower bound for growing `n`, nothing separates
complexity classes, and nothing bears on P vs NP: the missing ingredient
for anything of that kind would be a lower-bound argument that works for
all input sizes `n` against all general circuits/algorithms, which a
finite enumeration at `n = 2` (and a capped look at `n = 3`) cannot
provide. All statements below are about the stated fixed `n` only.

## Model

- Inputs are the variables `x0, ..., x_{n-1}` only.
- **No free constants**: 0 and 1 are not starting signals.
- **No free complemented inputs**: `NOT xi` is not a starting signal.
- Only gate: binary NAND, fan-in exactly two, repetition allowed
  (`NAND(s, s) = NOT s`).
- Unlimited fanout: any computed signal may feed any later gate
  (DAG sharing; circuits are DAGs, not formulas/trees).
- Output may be any input or computed signal. Size = number of gates.
- Truth tables are bit masks. Assignment `a` in `[0, 2^n)` gives `xi`
  the value of bit `i` of `a`; a function's mask has bit `a` set iff it
  outputs 1 on assignment `a`. For `n = 2` (assignment order
  `(x0,x1) = 00, 10, 01, 11`): `x0 = 1010`, `x1 = 1100`,
  `XOR = 0110` (mask 6), `XNOR = 1001` (mask 9).

## Method

`circuit_lab.py` runs breadth-first search over **states**, where a
state is the *set* of truth-table masks available so far (inputs plus
every distinct function built). One gate adds `NAND(u, v)` for `u, v`
in the state; if the result is already present, the gate is omitted.
Omitting duplicate functional signals is sound: such a gate changes
neither the available set nor anything a later gate can compute, so
removing it from any circuit is harmless. Because states keep the whole
set of shared subfunctions, DAG sharing is priced exactly; no
independent single-function cost recurrence (which would charge shared
subcircuits repeatedly) is used anywhere.

BFS layers count gates exactly (layer `d` states have built `d` new
functions). The first layer containing a function gives its exact
minimum, with parent pointers yielding a reconstructable witness:
signals `0..n-1` are inputs, gate `k` produces signal `n+k` from two
earlier signals, and `output` names the result signal. Every witness is
re-verified by `_simulate_per_assignment`, an independent per-assignment
Boolean simulation sharing no code with the mask-based search. The
unpruned syntactic enumeration `syntactic_min_costs` (every
topologically ordered gate sequence, ordered fan-in pairs, nothing
pruned) serves as an independent oracle for differential testing.

For `n = 3` the search takes strict caps (`max_gates`, `max_states`,
`max_states_per_layer`, `max_nodes`, CPU `timeout_seconds`). Unreached
functions are reported as `UNKNOWN`, never as numbers, and
`completed_layers` counts only fully generated gate layers, so no lower
bound beyond a completed layer is ever claimed.

## Results: n = 2, exhaustive (all 16 functions)

Search completed all layers (not truncated): visited states 195,
states per layer `[1, 3, 10, 27, 56, 98]`, completed layers 5. Exact
minimum NAND sizes (gates), each with an independently verified
witness:

| mask | function | min gates | mask | function | min gates |
|---|---|---|---|---|---|
| 0 | const 0 | 3 | 8 | AND | 2 |
| 1 | NOR | 4 | 9 | XNOR | 5 |
| 2 | x0 AND NOT x1 | 3 | 10 | x0 | 0 |
| 3 | NOT x1 | 1 | 11 | x1 implies x0 | 2 |
| 4 | NOT x0 AND x1 | 3 | 12 | x1 | 0 |
| 5 | NOT x0 | 1 | 13 | x0 implies x1 | 2 |
| 6 | XOR | 4 | 14 | OR | 3 |
| 7 | NAND | 1 | 15 | const 1 | 2 |

Headline cases, verified rather than assumed:

- **XOR = exactly 4.** Witness (BFS-found, independently verified):
  gates `[[0,1],[2,0],[2,1],[4,3]]`, output signal 5 — i.e.
  `s2 = NAND(x0,x1)` shared by `s3 = NAND(s2,x0)` and
  `s4 = NAND(s2,x1)`, then `NAND(s4,s3)`. The syntactic oracle confirms
  XOR is absent up to 3 gates and first appears at 4.
- **XNOR = exactly 5.** Witness: gates
  `[[0,0],[2,1],[2,3],[0,1],[5,4]]`, output signal 6. The syntactic
  oracle confirms XNOR is still absent at 4 gates; the BFS reaches it
  first at layer 5.

Differential check: for every function, the BFS minimum agrees with
the unpruned syntactic oracle restricted to <= 3 gates (syntactic
sequence counts per length: 1, 4, 36, 576), and functions absent from
the oracle at <= 3 gates are exactly those with BFS minimum > 3.
Tampered witnesses (wrong output signal, future signal reference,
out-of-range gate input) all fail verification, as tested.

## Results: n = 3, capped (illustrative, incomplete)

Example capped run (`max_gates=4, max_states=20000,
max_states_per_layer=20000, max_nodes=20000, timeout=20s`): truncated
at the depth cap, `completed_layers = 4`, states per layer
`[1, 6, 36, 206, 1252]`, 1501 visited states, 91 of 256 functions
reached with exact verified witnesses (e.g. 3-input AND, mask 128, in
4 gates); the other 165 are `UNKNOWN`. Reached values are exact;
unreached values carry no claimed bound beyond `completed_layers`.

## Lean proof (CircuitBounds.lean)

Core Lean only (no imports beyond the prelude), same model and mask
convention as above (`x0 = 10`, `x1 = 12`, XOR target mask 6). A
circuit of length `k` is enumerated as ordered fan-in choices with
sharing (gate `i` picks from the `2 + i` earlier signals, output picks
any of `2 + k` signals), giving `circuitsUpTo3` with
2 + 12 + 144 + 2880 = 3038 entries across lengths 0-3. Two theorems are
proved by `decide` (kernel checking; the file contains no other proof
automation for these):

- `xor_no_circuit_up_to_3`: every circuit with at most 3 NAND gates
  computes a mask different from XOR's — so XOR needs >= 4 gates.
- `xor_witness_4`: the explicit witness `[(0,1),(0,2),(1,2),(3,4)]`
  (output signal 5, the shared-`NAND(x0,x1)` circuit above) computes
  XOR — so 4 gates suffice, and the exact minimum is 4.

Verified in this session with
`C:/Users/email/.elan/bin/lean.exe CircuitBounds.lean` (Lean 4.35.0,
exit 0, ~4 s). The file ends with print-axioms directives; observed
output:

```text
'xor_no_circuit_up_to_3' depends on axioms: [propext]
'xor_witness_4' depends on axioms: [propext]
```

`propext` is Lean's standard core logical axiom (used internally by the
decision procedure); no user-declared axioms and no incomplete proofs
are present, which the printed output confirms (no `sorryAx`).

## Reproduction

```powershell
python -m unittest tests.test_circuit_lab        # stdlib runner, no deps
python circuit_lab.py --n 2                       # full JSON, real witnesses
python circuit_lab.py --n 3 --max-gates 4 --max-states 20000 --timeout 20
C:/Users/email/.elan/bin/lean.exe CircuitBounds.lean
```

Resource bounds: the `n = 2` search is exhaustive and finishes in well
under a second (195 states). The `n = 3` defaults are capped at
6 gates / 100000 states / 30 s CPU and always degrade to `UNKNOWN`
rather than to an overclaimed bound. The Lean check is a single finite
kernel computation over 3038 circuits (a few seconds).

## What is not claimed

Exact minima are established here only for `n = 2` (complete) and for
whatever a capped `n = 3` run happens to reach. There is no claim about
growing `n`, no asymptotic or superpolynomial lower bound, and no
consequence for P vs NP or for general circuit complexity; a finite
enumeration cannot supply the all-`n`, all-circuits argument such
claims would require.
