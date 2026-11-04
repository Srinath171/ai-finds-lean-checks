# General parity sample minimum against zero/one NAND gate

**VERIFIED for general input width.** `frontier/ParityTeaching.lean` compiles with Lean 4.35.0 and project `LEAN_PATH`, exit code **0**, without warnings. Its printed dependencies are only standard Lean axioms (`propext`, `Quot.sound`, and, for the odd-width lower bound, `Classical.choice`). No placeholders, native decision procedure, unsafe code, or additional axioms are used.

## Exact theorem and model

For every even n≥2, exactly **two** assignments are needed to distinguish n-bit parity from every well-formed circuit with at most one binary NAND gate. For every odd n≥3, the exact minimum is **three**.

The circuit model has n variable inputs, no free constants or complemented inputs, repeated gate fan-ins, unrestricted fanout, and an output selected from any input or computed gate. Thus its zero/one-gate functions are precisely projections xi and NAND(xi,xj), including NOT(xi)=NAND(xi,xi).

The file first defines this function class independently as `ParityTeaching.SmallFn n` using `Fin n` variable indices. It then **proves**, rather than assumes, the equivalence to the project's independently well-formed topological circuits:

- `small_circuit_classified`: every well-formed circuit of size at most one denotes a member of `SmallFn n` on every valid n-bit assignment.
- `smallFn_implemented`: every member has a well-formed implementation of size at most one.
- `separates_iff_circuits`: on valid samples, separation from the two representations is equivalent.

The final model-level theorems are `odd_circuit_minimum_three` and `even_circuit_minimum_two`. Samples are finite lists of Boolean lists, each row constrained to length n; the explicit upper-bound samples are additionally proved duplicate-free (`odd_samples_nodup`, `even_samples_nodup`), so their list lengths are their assignment-set cardinalities.

## Odd-width lower bound: two examples always have a matching small circuit

`parity_complement` proves the general identity: complementing all coordinates flips parity at odd width and preserves parity at even width. The proof is structural induction with exact parity-of-length arithmetic.

For two odd-width assignments u,v, let their parity labels be p,q. If no projection xi and no complement NOT(xi) matches both labels, each coordinate column must avoid (p,q) and its complement.

- If p=q, the only allowed columns are 01 and 10, so v is the coordinatewise complement of u. Odd-width complement parity then gives q=NOT(p), a contradiction.
- If p≠q, the only allowed columns are 00 and 11, so the assignments are identical, forcing equal parity labels, another contradiction.

This is formalized in `pair_matching_column`, `pair_matching_smallFn`, and `odd_no_two_samples`. The lower bound already holds against the projection/NOT subclass and therefore against the full zero/one-gate class.

For any positive width, a single assignment is matched by a projection or its complement (`one_matching_smallFn`), giving the even-width lower bound of two.

## Explicit upper bounds

For even n, use the all-zero and all-one assignments. Both parity labels are zero. Every projection disagrees on the all-one row; every NAND pair disagrees on the all-zero row.

For odd n≥3, use these three parity-zero assignments:

1. all zero;
2. all one except coordinate 0;
3. all one except coordinate 1.

Every NAND pair disagrees on the all-zero row. Every projection is one on at least one of the other two rows, and so disagrees there. Lengths, labels, coverage of every coordinate, and distinctness of these assignments are proved for arbitrary n in the stated ranges.

## Scope and limits

This is a general theorem for infinitely many widths, not a finite-range experimental extrapolation. However the competitor circuit-size budget is fixed at one, and the exact sample minimum remains the constant two or three. It supplies no omega(s) asymptotic, lower bound against growing circuit sizes, NP-membership claim, or complexity-class separation. The file does not assert parity is absent from all size-at-most-two circuits at every relevant n; that is a separate premise needed for a broader AC2 application. No novelty claim is made.

The boundary n=1 is intentionally excluded from the exact-minimum statements: parity is itself a projection in the competitor class, so it cannot be distinguished from every member by any sample set.

## Replay

After the current project dependency artifacts are built:

```powershell
$env:LEAN_PATH = (Get-Location).Path
& "$env:USERPROFILE\.elan\bin\lean.exe" frontier\ParityTeaching.lean
```

Only this proof and this note were added for the task. No API calls, keys, network resources, or unrelated computer files were used.
