# Lexicographic counterexample: independent local audit

**PASS for the stated finite claim.** An independent invocation of Lean 4.35.0 compiled `frontier/LexCounterexample.lean` with project `LEAN_PATH`, using the existing `CircuitCoverage.olean`, and exited 0. All eight printed theorem dependencies contain only standard Lean axioms (`propext`, `Quot.sound`, and, in the inherited XOR lower-bound chain, `Classical.choice`). No placeholder, custom axiom, native decision procedure, unsafe declaration, or executable IO was found.

## Precisely what the accepted theorem refutes

The model has two variable inputs, binary NAND gates, repeated fan-ins, unlimited sharing, no free constants or complemented inputs, and a well-formed output selector. At gate threshold zero, only masks 10 and 12 (the input projections) are computable. Therefore mask 0 is the first missing mask in numeric order. A valid three-gate circuit computes mask 0, while the existing complete XOR lower bound proves mask 6 is not computable with three gates. Thus the first missing mask at threshold zero is not maximally hard among two-input functions.

The witness is `[(0,0), (2,0), (3,3)]` with output 4: NOT x0, then constant one, then constant zero. The result needs only an upper bound of three gates for zero, not an exact minimum. Its use of the XOR lower bound quantifies over all well-formed circuits, not merely sampled circuits.

## Ordering and scope

Numeric mask order and lexicographic bit-string order generally differ with the project's least-significant-bit-first assignment convention. This particular counterexample survives either ordinary lexicographic order with 0 before 1: the all-zero truth table is first in both. The Lean theorem itself formalizes numeric order only.

The `LexFirstMissing` definition does not itself require the mask to be below 16, and `MaximallyHard` can be vacuous for an uncomputable mask. Neither issue invalidates this witness: mask 0 is in range and is explicitly computable with three gates. The threshold-zero example refutes an unrestricted assertion covering zero; it does not by itself refute a differently restricted assertion requiring positive or growing thresholds.

This is a finite counterexample to an extrapolation, not a P-versus-NP result or an asymptotic lower bound.

## Verification versus coding-agent termination

The generating Muse session reached its tool-step budget and reported a failed termination. That is a workflow outcome, not a Lean rejection of the final saved file. The parent separately compiled the saved proof successfully; this audit independently reproduced exit code 0. Acceptance here refers to those kernel checks of the on-disk artifact, not to the generating agent's status message.

No source files were modified by this audit. No unrelated files, credentials, or network services were accessed.
