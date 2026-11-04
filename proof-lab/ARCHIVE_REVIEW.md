# User archive review

Reviewed 2026-11-04. Source: `../files/files.zip` relative to this proof-lab directory.

SHA-256: `18a21ec6dd81b6598cd41b09917ebf48be561e892be5a245a90952dc721daf6c`

## Contents and value

The archive contains `README.md`, `prover.py`, `app.py`, `theorems.json`, `requirements.txt`, and a nested `witness.zip`. The nested archive contains text-identical copies of the five source/data files under `witness/`.

This is a small "Witness" proof-demo template. `prover.py` implements model generation, Lean checking, error feedback, attempt logging, and model summaries. `app.py` supplies a Streamlit theorem picker and benchmark display. The useful ideas are the attempt visualization and small certificate-finding examples.

`theorems.json` has 15 exercises: ten elementary arithmetic/list/logic statements and five fixed puzzles involving SAT, a perfect square, two numbers, subset sum, and graph coloring. Each includes a reference proof. A data-only copy is saved at `references/witness-theorems.json`, with provenance and an explicit unverified status. The catalog was inspected for unexpected commands and control characters; no theorem was executed or proved during this review.

## Mathematical limits

No P-versus-NP proof, new lower bound, general algorithm, asymptotic analysis, research paper, or recorded benchmark results are present. The results table in `README.md` is blank. Fixed puzzle solutions and elementary identities are useful smoke tests but do not settle P versus NP. The phrase "finding a proof is hard; checking one is easy" is an illustration, not a complexity theorem established by this project.

## Integration cautions

Keep the existing hardened prover. The archived verifier relies on a keyword blacklist, Lean exit status, and a check for "sorry" in output. It has no explicit axiom audit or execution sandbox. The model loop has no spending ceiling or output-token cap; Spark pricing is unspecified, and the stated Wonder price was not independently checked. API configuration reads environment variables and does not load `.env` itself. Model availability, installation instructions, reference proofs, and advertised costs were not tested.

Archive scripts and embedded setup commands were not executed. No source modules were imported into the working project; only this review and the explicitly unverified theorem data were added. No secrets were present in the reviewed entries, and no content was uploaded.