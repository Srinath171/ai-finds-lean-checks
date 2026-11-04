# Research checkpoint

P vs NP remains unsolved in this project. No polynomial-time SAT algorithm, explicit hard NP family, or separation is claimed.

## Verified results

- All 30 saved model benchmark proof bodies pass offline replay through the hardened Lean checker.
- SATSearch.lean proves exhaustive finite Boolean-search soundness, completeness, and enumeration size.
- CircuitBounds.lean and CircuitCoverage.lean prove two-input XOR needs exactly four NAND gates under the stated model, including coverage of all well-formed circuits.
- CircuitCounting.lean proves the general exact syntactic circuit count and an explicit upper bound, with a finite pigeonhole corollary.
- CircuitSemantics.lean proves pointwise Boolean correctness and the finite truth-table mask correspondence.
- HardFunction.lean combines these into a conditional nonconstructive hard-Boolean-function existence theorem.
- Independent reviewers replayed the formal sources and inspected their exact quantifiers and standard axiom dependencies.

## Computational evidence

- Spark MAX and Wonder MAX each proved 15/15 fixed elementary catalog exercises.
- The independent SAT solvers agree on 24 saved cases.
- Z3 synthesis and exhaustive BFS agree on every one of the 16 two-input functions.
- Three-input parity has an eight-gate witness; Z3 reports budgets zero through seven UNSAT. This is bounded solver evidence, separate from the Lean proofs.

## Remaining mathematical blocker

The counting theorem produces an unnamed hard Boolean function. It does not give a single explicit language in NP with superpolynomial circuit complexity. Such a result would also need careful uniformity and asymptotic statements; finite experiments cannot supply them. NP not contained in P/poly would imply P != NP, but that stronger nonuniform separation is not proved here.

The results reproduce known elementary counting and circuit facts. They are reusable, checked building blocks, not a new solution to P vs NP.

## Reproduction

Run `./verify.ps1` from this directory. It runs project tests and compiles all six formal research sources without API calls. Temporary verification files stay within the project.

The local dashboard is `http://127.0.0.1:8501`. API secrets remain in the ignored parent `.env`; logs and the private spending ledger are ignored by Git.

Meta's local ceiling is $125 and Claude API's is $40. Reservations govern cooperating project callers only. External holds are reserves rather than actual invoices; provider billing can be delayed. See saved token estimates for completed metered runs.

Final verification: 149 tests passed; all six research Lean sources compiled. No paid model request remains running from this checkpoint.
