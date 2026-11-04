# Explicit exponential counting schedule: formal result

**VERIFIED in Lean 4.35.0.** `frontier/ExplicitSchedule.lean` compiled with project `LEAN_PATH`, exit code **0**. The three printed theorem dependencies contain only `propext`, `Classical.choice`, and `Quot.sound`; no placeholders or custom axioms occur.

## Accepted general inequality

For every natural number n with n≥16, define k=floor(n/4) and s=2^k. The theorem `explicit_schedule_counting_inequality` proves, with exact natural-number arithmetic:

```text
(s+1) * (n+s)^(2*s+1) < 2^(2^n).
```

The proof uses no logarithms, approximations, floating-point calculations, or finite-range substitution for the all-n argument.

`schedule_linear_bounds` proves by induction that k≥4 implies both `4*k+3 ≤ 2^(k+1)` and `k+2 ≤ 2^k`. Together with division bounds `4*k ≤ n ≤ 4*k+3`, these give `n ≤ 2*s`, `k+2 ≤ s`, and `s≥16`. In particular the argument handles n=17,18,19 without the false intermediate claim n≤s.

Writing `E=(k+1)+(k+2)*(2*s+1)`, the formal inequality chain is:

```text
(s+1)*(n+s)^(2*s+1) < 2^E,
E ≤ 2*s²+2*s ≤ 3*s² < s⁴ = 2^(4*k) ≤ 2^n.
```

Strict monotonicity of powers of two gives the required conclusion.

## Accepted hard-function existence theorem

The accepted general inequality is supplied to the existing `exists_hard_bool_function` theorem. The resulting declaration is:

```lean
exists_hard_bool_function_explicit_schedule (n : Nat) (hn : 16 ≤ n) :
  ∃ f : Nat → Bool, ∀ (seq : List (Nat × Nat)) (out : Nat),
    WellFormedCircuitN n seq out → seq.length ≤ 2 ^ (n / 4) →
      ∃ j, j < 2 ^ n ∧ evalCircuitBool n j (seq, out) ≠ f j
```

This covers every independently well-formed topological circuit at the fixed exponential gate threshold, using the previously verified pointwise Boolean NAND semantics. The model remains binary NAND with variable inputs, no free constants or complemented inputs, repeated fan-ins, unrestricted sharing, and any input/gate output selector.

## Exact scope

The threshold is a single prescribed schedule `s(n)=2^(floor(n/4))`, rather than a schedule chosen separately for each polynomial degree. The theorem establishes hard Boolean functions at that schedule for every n≥16.

The existential function is not selected or implemented by this file. In particular, this file does not formalize the lexicographic/mex construction or prove its computability, runtime, or membership in a complexity class. The original informal `EXPLICIT_SCHEDULE.md` describes that construction separately. No NP verifier, explicit hard NP language, P/poly-membership classification, novelty claim, or P-versus-NP separation is supplied.

## Replay

After building current project dependency artifacts:

```powershell
$env:LEAN_PATH = (Get-Location).Path
& "$env:USERPROFILE\.elan\bin\lean.exe" frontier\ExplicitSchedule.lean
```

Only the two new schedule files were written for this task. No unrelated computer files, credentials, network services, or external models were accessed.
