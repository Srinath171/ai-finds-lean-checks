# SAT search laboratory — what is proved, what is tested, what remains open

This note accompanies three new artifacts and modifies nothing else:

- [sat_lab.py](sat_lab.py) — an educational SAT experiment module (Python standard library only).
- [tests/test_sat_lab.py](tests/test_sat_lab.py) — solver-independent checks for that module.
- [SATSearch.lean](SATSearch.lean) — a Core Lean 4 (toolchain-pinned v4.35.0) formalisation of exhaustive finite search.

No network access and no API key are needed for any of it:

```powershell
.venv\Scripts\python.exe -m unittest tests.test_sat_lab -v
.venv\Scripts\python.exe sat_lab.py bench --output sat_bench_results.json
C:\Users\email\.elan\bin\lean.exe SATSearch.lean
```

## 1. The Python module

Representation: a formula is a sequence of clauses, each a sequence of non-zero integer literals; literal `k > 0` is variable `k`, `k < 0` is its negation, variables are `1..num_vars`. `validate_cnf` rejects booleans, `0`, non-integers, strings, and literals beyond `num_vars`. An assignment is a dict with exactly the keys `1..num_vars` and boolean values, or a sequence of exactly `num_vars` booleans; `verify_assignment` is a direct, separate checker that raises on malformed input and otherwise reports whether every clause has a true literal.

Two solvers share the `SAT` / `UNSAT` / `UNKNOWN` protocol:

- `brute_force_solve` enumerates all `2 ** num_vars` assignments in a fixed order (variables ascending, `False` before `True`).
- `dpll_solve` is DPLL with unit propagation only (no clause learning, no pure-literal elimination), branching on the smallest unassigned variable, `False` before `True`.

Both instrument **deterministic counters** — search nodes (candidate assignments for brute force; recursive calls for DPLL), literal inspections, decisions, and unit propagations. These counters are exact counts of search work, not clock measurements; **no complexity claim is inferred from timing anywhere in this project**, and the benchmark JSON stores counters (plus statuses), not speed-based conclusions. Exhausting `max_nodes` or `timeout_seconds` returns `UNKNOWN` with no assignment — a capped run never claims `UNSAT`. `generate_random_3cnf` is seed-deterministic; `pigeonhole_cnf` encodes the pigeonhole principle (known `UNSAT` when pigeons exceed holes) as a simple adversarial family for DPLL without learning.

## 2. Empirical evidence (tests, not proofs)

[tests/test_sat_lab.py](tests/test_sat_lab.py) uses its own satisfaction predicate, written directly from the definition, as the oracle — it does not reuse solver code to judge solvers. It establishes agreement between brute force, DPLL, and the oracle on:

- **every** formula over n = 2 variables (all 512 subsets of the 9 possible clauses);
- every formula of up to 3 clauses over n = 3, and seeded random 3-CNF instances up to n = 6;
- all [seeded instances in sat_lab.py](sat_lab.py) whose expected status is fixed by construction (empty formula/clause, contradictory units, pigeonhole cases);
- corruption handling: malformed formulas and assignments (missing/extra variables, non-boolean values, literal `0`, out-of-range literals) raise or fail verification, and flipping a forced variable in a returned model breaks verification;
- caps: with `max_nodes` in {0, 1, 2} on a formula that needs full search, both solvers return `UNKNOWN`, never `UNSAT`; repeated runs return identical statuses, assignments, and counters;
- the bench CLI: it writes a JSON file whose per-instance solver statuses agree whenever neither side is `UNKNOWN`.

Passing observed in this session: 12 unit tests, all passing (`python -m unittest tests.test_sat_lab`), and the bench command writing 24 instance records with 0 solver disagreements. These are finite checks on small instances — evidence of correct implementation, not a theorem about all inputs.

## 3. The precise Lean theorem

[SATSearch.lean](SATSearch.lean) is self-contained Core Lean 4 with no placeholder proofs, no added axioms, no kernel-bypassing decision procedures, and no unsafe code. Its definitions are:

- `findSat p l` — the first element of list `l` (in list order) whose Boolean predicate `p` returns `true`, else `none`;
- `allAssignments n` — the recursively built list of all Boolean lists built by prefixing `false`/`true` to every length-`n` list;
- `lookupVar`, `evalLit`, `evalClause`, `evalCNF` — Boolean evaluation of a concrete CNF (literal = 0-based variable index plus polarity) under a list assignment;
- `satSearch n p = findSat p (allAssignments n)` and `cnfSearch n f = satSearch n (fun a => evalCNF a f)`.

Proved statements (names as in the file):

| Theorem | Statement |
|---|---|
| `findSat_sound` | `findSat p l = some a` implies `a ∈ l` and `p a = true`. |
| `findSat_isSome_of_mem` | If `a ∈ l` and `p a = true`, then `findSat p l = some b` for some `b` with `p b = true` and `b ∈ l`. |
| `findSat_eq_none_iff` | `findSat p l = none` iff every `a ∈ l` has `p a = false`. |
| `length_of_mem_allAssignments` | Every member of `allAssignments n` has length `n`. |
| `mem_allAssignments` (coverage) | Every Boolean list of length `n` is a member of `allAssignments n`. |
| `allAssignments_length` | The enumeration has exactly `2 ^ n` entries. |
| `satSearch_sound`, `cnfSearch_sound` | A returned assignment has length `n` and makes the predicate (resp. the CNF) evaluate to `true`. |
| `satSearch_complete`, `cnfSearch_complete` | If any length-`n` assignment satisfies the predicate (resp. CNF), the search returns one that does. |
| `satSearch_eq_none_iff`, `cnfSearch_eq_none_iff` | The search returns `none` iff no length-`n` assignment satisfies the predicate (resp. CNF). |

In words: **exhaustive search over the enumerated assignments is sound and complete relative to that finite enumeration, and the enumeration covers the whole finite assignment space.** The `#print axioms` audit at the end of the file, run in this session, reports only the standard `propext` and `Quot.sound` (no `sorryAx`, no project-added axioms) for every result above.

Scope limits of the formal result, stated plainly: it is about *this list search* over *Boolean lists*; it does not formalise DPLL, unit propagation, or the Python code, and it proves nothing about how long search takes. The enumeration still has `2 ^ n` entries — the proved count theorem says so.

## 4. What would remain to solve P vs NP

SAT is NP-complete (Cook–Levin), so resolving P vs NP via SAT means one of exactly two general statements, neither of which is approached here:

1. **P = NP route:** a single algorithm that decides *every* CNF formula in time polynomial in the input size — a uniform polynomial upper bound covering the worst case over all formulas, plus a proof of that bound; or
2. **P ≠ NP route:** a proof that *no* algorithm decides SAT in polynomial time — a super-polynomial worst-case lower bound for all algorithms, not just for brute force or for DPLL.

Exhausting finite instances (the Python tests) and proving an exhaustive searcher sound and complete (the Lean file) contribute to neither: both are fully consistent with SAT requiring exponential time in the worst case, and the Lean count theorem actively records the `2 ^ n` size of naive enumeration. Nothing in this project exhibits a polynomial-time SAT algorithm, proves a super-polynomial lower bound, or claims any complexity separation or collapse.

Known barriers are relevant only as explanations of why the two routes above are hard; they are limitations, and this project does not bypass any of them:

- **Relativisation (Baker–Gill–Solovay):** arguments that diagonalise uniformly against all machines also work relative to suitable oracles where the answer differs, and oracle worlds exist with both P = NP and P ≠ NP — so purely relativising techniques cannot settle the question either way.
- **Natural proofs (Razborov–Rudich):** a circuit lower-bound proof that is "natural" (constructive and large) would contradict the pseudorandomness that standard cryptographic assumptions provide, so such proofs are unlikely to yield the strong lower bounds route 2 would need in circuit form.
- **Algebrisation (Aaronson–Wigderson):** even techniques that escape relativisation by arithmetising formulas face oracle extensions where again both answers occur, so algebraic methods alone, as currently used, also do not settle it.

A genuine resolution needs a method outside the reach of these limits (or a proof that a limit does not apply), a general worst-case bound of one of the two kinds above, and verification of that proof. Until then: **this project does not solve, and does not claim to solve, P vs NP** — it is a small, verified-correct exhaustive-search laboratory plus an empirical test bench for tiny instances.
