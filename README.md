# AI Finds, Lean Checks

**Meta models search for proofs. Lean decides what is true.**

Finding a solution is hard; checking one is easy. That gap is the heart of P vs NP. This project turns it into a working system: **Muse Spark** and **Muse Wonder** propose Lean 4 proofs, a hardened checker verifies them, and Lean's errors go back to the model until a proof is accepted or the attempt budget runs out.

Built for the **Meta Global AI Developer Hackathon** (Oct 26 – Nov 4, 2026), Indie track, theme: Push the Frontier.

**Demo video:** _add link here_

## For judges

- **What it is:** a generate-and-check loop where Meta models write proofs and Lean 4 verifies them, plus SAT and NAND-circuit labs that make "finding vs. checking" concrete.
- **Meta AI used:** Muse Spark 1.3 and Muse Wonder 1.0 through the Meta Model API (prover), and Muse Spark 1.3 in the chat demo.
- **Result:** both models proved **15/15** benchmark theorems, each verified by Lean (table below).
- **Depth:** 29 Lean research modules replayed; 353 Python tests passing.
- **Honest scope:** this does not solve P vs NP. The theorems reproduce known results; the contribution is the verified pipeline and its finite experiments.

## Results

Recorded Nov 4, 2026, same 15 fixed theorems, effort max, Lean 4.35.0.

| Model | Verified | Attempts | Avg attempts | Input / output tokens | Est. cost |
|---|---|---|---|---|---|
| Muse Wonder 1.0 | 15/15 (100%) | 15 | 1.00 | 3,022 / 4,508 | $0.102 |
| Muse Spark 1.3 | 15/15 (100%) | 16 | 1.07 | 3,296 / 19,384 | $0.087 |

Costs are token-usage estimates, not invoices.

## How it works

1. The theorem's name and statement come from a fixed local catalog; the model supplies only the proof body.
2. A conservative allowlist rejects `sorry`, `admit`, `axiom`, `native_decide`, imports, and metaprogramming.
3. Lean 4.35.0 compiles the proof with `#print axioms`; only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
4. If Lean rejects the proof, its diagnostics go back to the model for another attempt.

## Verified highlights (Lean)

- Exhaustive SAT search over n Boolean variables is sound and complete (`SATSearch.lean`).
- Two-input XOR needs exactly 4 NAND gates in the stated circuit model (`CircuitBounds.lean`, `CircuitCoverage.lean`).
- Counting argument: for large enough n, some Boolean function has no small NAND circuit (`HardFunction.lean`, `ExplicitSchedule.lean`). A known, nonconstructive result, formalized here.

Full details and exact scope: [proof-lab/README.md](proof-lab/README.md).

## Run it

**Proof lab** (Windows, from `proof-lab/`; needs Python 3.11+ and the pinned Lean 4.35.0 toolchain via elan):

```powershell
py -m venv .venv
.\.venv\Scripts\Activate.ps1
python -m pip install -r requirements.txt
python prover.py preflight
python -m streamlit run app.py
python prover.py prove nat_add_comm --model muse-spark-1.3
python demo.py   # offline demo with canned proofs, no API calls
```

Set `MODEL_API_KEY` (a Meta Model API key) in the shell or in the repo's `.env`, which is never committed.

**Chat demo** (repo root; needs Node.js 20.6+):

```powershell
Copy-Item .env.example .env   # then set MODEL_API_KEY
node --env-file=.env server.js
```

Open http://localhost:3000. Run tests with `npm test`.

The chat server binds to localhost, reads the key only from the environment, validates and size-limits input, never forwards upstream error bodies, and renders replies with `textContent`.

## Repository layout

- `proof-lab/`: prover, Lean modules, SAT and circuit labs, tests
- `server.js`, `public/`: Muse Spark chat demo
- `tests/`: chat demo tests

## Tools and disclosure

Built during the hackathon window. Meta models do the proving in the benchmark. Development also used Claude Code, the Claude API (optional critiques via `research_client.py`), and Cursor. Model output is never accepted as a theorem unless Lean verifies it.
