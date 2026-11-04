# Research checkpoint

P vs NP remains unsolved. No polynomial-time SAT algorithm, explicit hard NP family, or separation has been established.

The latest completed offline verification passed **207 Python tests and twelve research Lean sources**, pinned to Lean 4.35.0. Exact source hashes are saved in results/verification.json. The original catalog, SAT-search, circuit counting, coverage, mask semantics, and conditional hard-function results remain accepted.

New accepted results:

- A formal counterexample to unrestricted first-missing-is-hardest at threshold zero.
- Two formally refuted antichecker conjectures: AND3 at n=3,s=3 requires at least four points against size-three circuits; parity at n=3,s=2 requires exactly three against size-one circuits.
- An all-n counting inequality for n>=16 at the fixed exponential threshold 2^(floor(n/4)), with a hard-function existence corollary in independent Boolean circuit semantics.

The key missing step remains a uniform polynomial-time NP verifier for a designated hard family. The computable lex-first construction has a huge enumeration upper bound; that does not establish NP membership or rule it out. The review in frontier/PROOF_ATTEMPT_REVIEW.md identifies further quantified and transfer gaps.

The explicit sample-interpolation builder and ten focused tests pass. The sharp mathematical NAND bound is 3+n+(2n+1)m. Lean now proves a complete circuit interpolator and the no-sample-distinguisher consequence with the looser bound 3+(3n+7)m. The general parity minima (two for even n>=2; three for odd n>=3) are also verified, including equivalence to all independently well-formed zero/one-gate circuits.

The first bounded API campaign stopped safely after two provider errors. Tiny connectivity and narrow MAX math requests succeeded afterward. A narrower follow-up campaign is active at this checkpoint, with the original 19:42 UTC deadline and at most ten further rounds, using Wonder MAX and regular Claude critique. Its proposals remain UNVERIFIED. Live status is in ignored frontier/campaign-followup/status.json; STOP there halts between calls. No solution or future progress is promised.

Claude API ceiling: $40. Latest checked local ledger settled $4.17783, with an additional $1 external-use hold, leaving $34.82217 available. This is cooperating-call accounting, not account-wide Anthropic billing. Meta ceiling: $125; conservative external holds cover coding/uncertain usage. Meta billing page currently stays on Loading billing, so no fresh provider balance is verified. Secrets and private ledger/raw logs remain ignored.

All access and edits remain limited to project files and the specific tools/accounts authorized for this task. Unrelated existing root app changes remain outside the research commit.
