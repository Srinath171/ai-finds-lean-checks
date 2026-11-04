# Essential-variable bound for shared NAND circuits

**VERIFIED general theorem.** `frontier/DependencyBound.lean` compiles with Lean 4.35.0 and project `LEAN_PATH`, exit code **0**, without warnings. Printed theorem dependencies contain only `propext`, `Quot.sound`, and (for the essential-input counting step) `Classical.choice`. No placeholders, additional axioms, native decision procedures, unsafe code, or external computation are used.

## Model and precise support statement

The model is the existing independently well-formed topological binary-NAND circuit: n variable inputs, ordered fan-in pairs, repetitions and unrestricted sharing, and an output selected from any input or gate output. Free constants and free complemented inputs are absent. Gates may be unused.

For every such circuit `(seq,out)`, `exists_small_support` proves that there is a list S of input indices such that:

- every index in S is less than n;
- `S.length ≤ seq.length + 1`;
- for every two Boolean assignment lists u,v of length n, agreement at all indices in S implies equal circuit outputs under the project's `runGatesBool` / `selBool` semantics.

S may contain repeated indices. This is harmless and explicit: its underlying finite set contains no more elements than its list length. The subsequent essential-variable theorem avoids assuming duplicate-freedom; it proves the required cardinality inequality directly against this list using the established finite-list pigeonhole lemma.

The result is a semantic dependence theorem on arbitrary valid Boolean input assignments, not merely a syntactic occurrence bound.

## Why sharing is counted correctly

The proof uses a backwards active-wire frontier, starting from the singleton output wire. When processing a gate whose output is active, `step` removes **all** occurrences of that output index and adds the two fan-in indices. When the output is not active, the frontier stays unchanged.

A processed active gate removes at least one list entry and adds two, so the list length increases by at most one (`step_length`). This remains true when fan-ins repeat, already occur in the frontier, or a shared gate output had several active occurrences. No shared circuit is unfolded into a formula and no formula-size bound is substituted for gate count.

`backward` processes the later gates first. On the original head/tail representation, the recursive tail treats the head gate's output as the next starting signal; the head is retired after that recursion. `wf_cons_iff` relates this indexing to the independently stated topological bounds.

`backward_bounded` proves that after all gates are retired only original input indices remain. `backward_agreement` proves the Boolean agreement invariant. Starting from one active output and processing s gates yields a sufficient input-support list of length at most s+1.

## Essential-variable consequence

`EssentialAt` says that two valid assignments can differ only in coordinate i yet produce different outputs. If every i<n is essential, every such i must belong to any sufficient support: otherwise those two assignments would agree on the entire support and the semantic invariant would force equal outputs.

The accepted theorems are:

```lean
essential_inputs_le_gates_add_one :
  WellFormedCircuitN n seq out →
  (∀ i, i < n → EssentialAt n seq out i) → n ≤ seq.length + 1

essential_inputs_le_budget_add_one :
  WellFormedCircuitN n seq out → seq.length ≤ s →
  (∀ i, i < n → EssentialAt n seq out i) → n ≤ s + 1
```

The explicit arguments in the file precede these hypotheses. Both statements quantify over all independently well-formed circuits, including arbitrary sharing, repeated fan-ins, zero-gate projections, and outputs that ignore later gates.

## Scope

This is the elementary linear lower bound s≥n−1 for a function whose n input variables are all essential. It is general in n and s, but it is not a superpolynomial lower bound, an NP-membership result, or a complexity-class separation. No novelty or P-versus-NP claim is made. Essentiality of a particular target function must be established separately before applying the theorem to that target.

## Replay

After the current project dependency artifacts are built:

```powershell
$env:LEAN_PATH = (Get-Location).Path
& "$env:USERPROFILE\.elan\bin\lean.exe" frontier\DependencyBound.lean
```

Only this new Lean file and this note were written for the task. No API calls, credentials, unrelated computer files, network resources, or external models were accessed.
