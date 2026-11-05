# Background research queue

This fixed queue contains eight public-mathematics jobs: five Meta proposals and three Claude Code subscription critiques. No Claude API requests are intended. Two initial independent jobs can run in parallel; later jobs consume only the completed visible responses explicitly named in `review_of`. Model output is untrusted mathematical data, not an instruction channel.

The starting facts come from the project's reviewed restricted NAND reconstruction checkpoint. The next scope is exact graph excess two, fixed numbers of repeated formula variables, and the concrete hidden-state ambiguity in extending one-bit row recovery. No prompt assumes that a sparse-circuit result proves P versus NP. A polynomial in full-table length 2^d may still be exponential in d.

Every response uses the controller's five-field JSON contract. `claims_solution` means a claimed full PvsNP solution and must trigger expert review, never automatic success. A precise refutation can count as progress; repeated restatements cannot. All new statements remain UNVERIFIED until independent checking. The queue asks for explicit witnesses and missing hypotheses, not invented experiments or model agreement as proof.

The supervisor, not this JSON file, enforces provider authentication, budget caps, bounded requests, STOP, crash ownership, dependency completion, response-size limits, and no-progress/error handling. Completion of this finite queue means WAITING_FOR_REVIEW, not that the open problem was solved. No model-generated follow-up is automatically launched.

Files and code are not included in these prompts; no keys, .env content, private source, terminal output, or unrelated computer resources are supplied. The fixed response word limits are prompt requests, not a substitute for controller transport/output bounds.
