"""Educational SAT experiment module (stdlib only).

Representation
--------------
A CNF formula is a sequence of clauses; a clause is a sequence of integer
literals.  Literal ``k > 0`` means variable ``k`` is true, ``k < 0`` means
variable ``-k`` is false.  Variables are numbered ``1..num_vars``.  An
assignment is either a ``dict`` mapping ``1..num_vars`` to ``bool`` or a
list/tuple of ``num_vars`` bools where index ``i`` holds variable ``i+1``.

Solvers report ``"SAT"``, ``"UNSAT"`` or ``"UNKNOWN"``.  ``"UNKNOWN"`` is
returned whenever a node cap or time cap is exhausted; a capped search never
reports ``"UNSAT"``.  Node and literal-check counts are deterministic
counters of search work.  They are not timing measurements and no complexity
conclusion should be drawn from wall-clock time.
"""
from __future__ import annotations

import argparse
import itertools
import json
import random
import time
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

CNF = Tuple[Tuple[int, ...], ...]
AssignmentDict = Dict[int, bool]

__all__ = [
    "CNFValidationError",
    "SearchStats",
    "SearchResult",
    "validate_cnf",
    "infer_num_vars",
    "validate_assignment",
    "verify_assignment",
    "brute_force_solve",
    "dpll_solve",
    "crosscheck",
    "generate_random_3cnf",
    "pigeonhole_cnf",
    "seeded_instances",
    "run_benchmark",
    "main",
]

STATUS_SAT = "SAT"
STATUS_UNSAT = "UNSAT"
STATUS_UNKNOWN = "UNKNOWN"


class CNFValidationError(ValueError):
    """Raised when a CNF formula or assignment is malformed."""


@dataclass
class SearchStats:
    nodes: int = 0
    literal_checks: int = 0
    decisions: int = 0
    unit_propagations: int = 0


@dataclass
class SearchResult:
    status: str
    assignment: Optional[AssignmentDict]
    stats: SearchStats = field(default_factory=SearchStats)
    num_vars: int = 0
    algorithm: str = ""

    def to_dict(self) -> dict:
        data = asdict(self)
        return data


def _is_int_literal(value: object) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


def validate_cnf(cnf: object, num_vars: Optional[int] = None) -> CNF:
    """Validate and normalize a CNF formula.

    Raises CNFValidationError on any malformed input: non-integer or boolean
    literals, literal 0, variables outside ``1..num_vars`` (when given), or
    non-sequence formulas/clauses (strings are rejected).
    """
    if num_vars is not None:
        if not _is_int_literal(num_vars) or num_vars < 0:
            raise CNFValidationError("num_vars must be a non-negative int")
    if isinstance(cnf, (str, bytes)) or not isinstance(cnf, (list, tuple)):
        raise CNFValidationError("CNF must be a list/tuple of clauses")
    normalized: List[Tuple[int, ...]] = []
    for clause in cnf:  # type: ignore[union-attr]
        if isinstance(clause, (str, bytes)) or not isinstance(clause, (list, tuple)):
            raise CNFValidationError("each clause must be a list/tuple of int literals")
        out_clause: List[int] = []
        for lit in clause:
            if not _is_int_literal(lit):
                raise CNFValidationError(f"literal must be an int, got {lit!r}")
            if lit == 0:
                raise CNFValidationError("literal 0 is invalid")
            if num_vars is not None and abs(lit) > num_vars:  # type: ignore[operator]
                raise CNFValidationError(
                    f"literal {lit} exceeds num_vars={num_vars}"
                )
            out_clause.append(lit)
        normalized.append(tuple(out_clause))
    return tuple(normalized)


def infer_num_vars(cnf: Sequence[Sequence[int]]) -> int:
    validated = validate_cnf(cnf)
    n = 0
    for clause in validated:
        for lit in clause:
            n = max(n, abs(lit))
    return n


def _resolve_num_vars(cnf: CNF, num_vars: Optional[int]) -> int:
    if num_vars is None:
        n = 0
        for clause in cnf:
            for lit in clause:
                n = max(n, abs(lit))
        return n
    return num_vars


def validate_assignment(assignment: object, num_vars: int) -> AssignmentDict:
    """Validate a complete assignment; return it as ``{var: bool}``.

    Accepts a dict with exactly the keys ``1..num_vars`` and bool values, or
    a list/tuple of exactly ``num_vars`` bools.  Anything else (missing or
    extra variables, non-bool values) raises CNFValidationError.
    """
    if not _is_int_literal(num_vars) or num_vars < 0:
        raise CNFValidationError("num_vars must be a non-negative int")
    if isinstance(assignment, dict):
        keys = set(assignment.keys())  # type: ignore[attr-defined]
        expected = set(range(1, num_vars + 1))
        if any(type(k) is not int for k in keys) or keys != expected:
            raise CNFValidationError(
                f"assignment keys must be exactly 1..{num_vars}, got {sorted(map(str, keys))}"
            )
        result: AssignmentDict = {}
        for var in range(1, num_vars + 1):
            value = assignment[var]  # type: ignore[index]
            if not isinstance(value, bool):
                raise CNFValidationError(f"assignment[{var}] must be bool, got {value!r}")
            result[var] = value
        return result
    if isinstance(assignment, (list, tuple)):
        if len(assignment) != num_vars:  # type: ignore[arg-type]
            raise CNFValidationError(
                f"sequence assignment must have length {num_vars}"
            )
        result = {}
        for idx, value in enumerate(assignment):  # type: ignore[union-attr]
            if not isinstance(value, bool):
                raise CNFValidationError(f"assignment[{idx}] must be bool, got {value!r}")
            result[idx + 1] = value
        return result
    raise CNFValidationError("assignment must be a dict or a list/tuple of bools")


def verify_assignment(cnf: object, assignment: object, num_vars: Optional[int] = None) -> bool:
    """Independent checker: True iff ``assignment`` satisfies every clause.

    This verifier is deliberately a direct, separate implementation from the
    solvers: it validates its inputs (raising on malformed data) and then
    checks each clause for at least one true literal.  An empty clause is
    never satisfied; an empty formula is satisfied by any complete
    assignment.
    """
    validated = validate_cnf(cnf, num_vars)
    n = _resolve_num_vars(validated, num_vars)
    model = validate_assignment(assignment, n)
    for clause in validated:
        clause_sat = False
        for lit in clause:
            value = model[abs(lit)]
            if (lit > 0 and value) or (lit < 0 and not value):
                clause_sat = True
                break
        if not clause_sat:
            return False
    return True


def _eval_formula_counted(
    cnf: CNF, model: AssignmentDict, stats: SearchStats
) -> bool:
    """Evaluate a complete assignment, counting every literal inspection."""
    for clause in cnf:
        clause_sat = False
        for lit in clause:
            stats.literal_checks += 1
            value = model[abs(lit)]
            if (lit > 0 and value) or (lit < 0 and not value):
                clause_sat = True
                break
        if not clause_sat:
            return False
    return True


def brute_force_solve(
    cnf: object,
    num_vars: Optional[int] = None,
    *,
    max_nodes: Optional[int] = None,
    timeout_seconds: Optional[float] = None,
) -> SearchResult:
    """Exhaustive search over all ``2**num_vars`` assignments.

    Enumeration order is deterministic: variables ``1..num_vars`` with
    ``False`` before ``True`` (itertools.product order).  One node is one
    candidate assignment examined.  Exhausting ``max_nodes`` or
    ``timeout_seconds`` yields UNKNOWN, never UNSAT.
    """
    validated = validate_cnf(cnf, num_vars)
    n = _resolve_num_vars(validated, num_vars)
    stats = SearchStats()
    start = time.monotonic()

    def _timed_out() -> bool:
        return timeout_seconds is not None and (time.monotonic() - start) >= timeout_seconds

    if max_nodes is not None and max_nodes <= 0:
        return SearchResult(STATUS_UNKNOWN, None, stats, n, "brute_force")
    for values in itertools.product((False, True), repeat=n):
        if _timed_out():
            return SearchResult(STATUS_UNKNOWN, None, stats, n, "brute_force")
        if max_nodes is not None and stats.nodes >= max_nodes:
            return SearchResult(STATUS_UNKNOWN, None, stats, n, "brute_force")
        stats.nodes += 1
        model: AssignmentDict = {i + 1: values[i] for i in range(n)}
        if _eval_formula_counted(validated, model, stats):
            return SearchResult(STATUS_SAT, model, stats, n, "brute_force")
    if _timed_out():
        return SearchResult(STATUS_UNKNOWN, None, stats, n, "brute_force")
    return SearchResult(STATUS_UNSAT, None, stats, n, "brute_force")


# ---------------------------------------------------------------- DPLL -----

_CLAUSE_SAT = "sat"
_CLAUSE_CONFLICT = "conflict"
_CLAUSE_UNIT = "unit"
_CLAUSE_OPEN = "open"


def _clause_state(
    clause: Tuple[int, ...],
    assignment: AssignmentDict,
    stats: SearchStats,
) -> Tuple[str, Optional[int]]:
    """Classify a clause under a partial assignment, counting literal checks."""
    unassigned_lit: Optional[int] = None
    unassigned_count = 0
    for lit in clause:
        stats.literal_checks += 1
        var = abs(lit)
        if var not in assignment:
            unassigned_count += 1
            unassigned_lit = lit
            continue
        value = assignment[var]
        if (lit > 0 and value) or (lit < 0 and not value):
            return (_CLAUSE_SAT, None)
    if unassigned_count == 0:
        return (_CLAUSE_CONFLICT, None)
    if unassigned_count == 1:
        return (_CLAUSE_UNIT, unassigned_lit)
    return (_CLAUSE_OPEN, None)


def dpll_solve(
    cnf: object,
    num_vars: Optional[int] = None,
    *,
    max_nodes: Optional[int] = None,
    timeout_seconds: Optional[float] = None,
) -> SearchResult:
    """DPLL with unit propagation (no clause learning, no pure-literal rule).

    Branching picks the smallest unassigned variable and tries ``False``
    then ``True``, so runs are deterministic.  One node is one recursive
    search call.  Exhausting ``max_nodes`` or ``timeout_seconds`` yields
    UNKNOWN, never UNSAT.
    """
    validated = validate_cnf(cnf, num_vars)
    n = _resolve_num_vars(validated, num_vars)
    stats = SearchStats()
    start = time.monotonic()
    exhausted = False

    def _timed_out() -> bool:
        return timeout_seconds is not None and (time.monotonic() - start) >= timeout_seconds

    def _over_cap() -> bool:
        return max_nodes is not None and stats.nodes >= max_nodes

    def _propagate(assignment: AssignmentDict) -> Optional[AssignmentDict]:
        """Unit-propagate to fixpoint; return None on conflict."""
        nonlocal exhausted
        current = dict(assignment)
        while True:
            if _timed_out():
                exhausted = True
                return None
            unit_lit: Optional[int] = None
            conflict = False
            for clause in validated:
                if _timed_out():
                    exhausted = True
                    return None
                state, lit = _clause_state(clause, current, stats)
                if state == _CLAUSE_CONFLICT:
                    conflict = True
                    break
                if state == _CLAUSE_UNIT and unit_lit is None:
                    unit_lit = lit
            if conflict:
                return None
            if unit_lit is None:
                return current
            stats.unit_propagations += 1
            current[abs(unit_lit)] = unit_lit > 0

    def _search(assignment: AssignmentDict) -> Optional[AssignmentDict]:
        nonlocal exhausted
        if exhausted:
            return None
        if _timed_out() or _over_cap():
            exhausted = True
            return None
        stats.nodes += 1
        propagated = _propagate(assignment)
        if propagated is None:
            return None
        # All clauses satisfied?  Variables not yet assigned can be False.
        all_sat = True
        for clause in validated:
            state, _ = _clause_state(clause, propagated, stats)
            if state != _CLAUSE_SAT:
                all_sat = False
                break
        if _timed_out():
            exhausted = True
            return None
        if all_sat:
            return {v: propagated.get(v, False) for v in range(1, n + 1)}
        # Branch on the smallest unassigned variable.
        branch_var: Optional[int] = None
        for var in range(1, n + 1):
            if var not in propagated:
                branch_var = var
                break
        if branch_var is None:
            # Complete assignment that does not satisfy the formula.
            return None
        stats.decisions += 1
        for value in (False, True):
            child = dict(propagated)
            child[branch_var] = value
            found = _search(child)
            if found is not None:
                return found
            if exhausted:
                return None
        return None

    if max_nodes is not None and max_nodes <= 0:
        return SearchResult(STATUS_UNKNOWN, None, stats, n, "dpll")
    found = _search({})
    if found is not None and not _timed_out():
        return SearchResult(STATUS_SAT, found, stats, n, "dpll")
    if exhausted or _timed_out() or _over_cap():
        return SearchResult(STATUS_UNKNOWN, None, stats, n, "dpll")
    return SearchResult(STATUS_UNSAT, None, stats, n, "dpll")


def crosscheck(
    cnf: object,
    num_vars: Optional[int] = None,
    *,
    max_nodes: Optional[int] = None,
    timeout_seconds: Optional[float] = None,
) -> dict:
    """Run both solvers and compare.  Raises AssertionError on disagreement.

    UNKNOWN results (from caps) are reported but do not count as
    disagreement; SAT assignments are checked with the independent verifier.
    """
    validated = validate_cnf(cnf, num_vars)
    n = _resolve_num_vars(validated, num_vars)
    brute = brute_force_solve(validated, n, max_nodes=max_nodes, timeout_seconds=timeout_seconds)
    dpll = dpll_solve(validated, n, max_nodes=max_nodes, timeout_seconds=timeout_seconds)
    for result in (brute, dpll):
        if result.status == STATUS_SAT:
            assert result.assignment is not None
            assert verify_assignment(validated, result.assignment, n), (
                f"{result.algorithm} returned a non-satisfying assignment"
            )
    agree = True
    if brute.status != STATUS_UNKNOWN and dpll.status != STATUS_UNKNOWN:
        agree = brute.status == dpll.status
        assert agree, f"disagreement: brute={brute.status} dpll={dpll.status} cnf={validated}"
        if brute.status == STATUS_SAT and dpll.status == STATUS_SAT:
            assert verify_assignment(validated, brute.assignment, n)  # type: ignore[arg-type]
            assert verify_assignment(validated, dpll.assignment, n)  # type: ignore[arg-type]
    return {"brute_force": brute, "dpll": dpll, "agree": agree, "num_vars": n}


# ------------------------------------------------------------- instances ---

def generate_random_3cnf(num_vars: int, num_clauses: int, seed: int) -> CNF:
    """Seeded random 3-CNF: each clause has 3 distinct variables.

    Deterministic for a given ``seed`` (uses a private ``random.Random``).
    """
    if not _is_int_literal(num_vars) or num_vars < 3:
        raise CNFValidationError("random 3-CNF needs num_vars >= 3")
    if not _is_int_literal(num_clauses) or num_clauses < 0:
        raise CNFValidationError("num_clauses must be a non-negative int")
    if not _is_int_literal(seed):
        raise CNFValidationError("seed must be an int")
    rng = random.Random(seed)
    clauses: List[Tuple[int, ...]] = []
    variables = list(range(1, num_vars + 1))
    for _ in range(num_clauses):
        chosen = rng.sample(variables, 3)
        clause = tuple(v if rng.random() < 0.5 else -v for v in chosen)
        clauses.append(clause)
    return validate_cnf(tuple(clauses), num_vars)


def pigeonhole_cnf(pigeons: int, holes: int) -> Tuple[CNF, int]:
    """Pigeonhole principle encoding; UNSAT when pigeons > holes.

    Variable ``(p-1)*holes + h`` means pigeon ``p`` sits in hole ``h``.
    Clauses state each pigeon occupies some hole and no hole holds two
    pigeons.  Small instances are a simple adversarial family for DPLL
    without clause learning (exponential behaviour is expected in general;
    no timing claim is made here).
    """
    if not _is_int_literal(pigeons) or not _is_int_literal(holes) or pigeons < 1 or holes < 1:
        raise CNFValidationError("pigeons and holes must be positive ints")

    def var(p: int, h: int) -> int:
        return (p - 1) * holes + h

    clauses: List[Tuple[int, ...]] = []
    for p in range(1, pigeons + 1):
        clauses.append(tuple(var(p, h) for h in range(1, holes + 1)))
    for h in range(1, holes + 1):
        for p in range(1, pigeons + 1):
            for q in range(p + 1, pigeons + 1):
                clauses.append((-var(p, h), -var(q, h)))
    num_vars = pigeons * holes
    return validate_cnf(tuple(clauses), num_vars), num_vars


def seeded_instances() -> List[dict]:
    """Named small instances with independently known expected status.

    Expected status follows from the construction (empty formula, empty
    clause, contradictory units, pigeonhole principle, random instances
    whose expectation is established by exhaustive brute force in tests).
    """
    php32, php32_n = pigeonhole_cnf(3, 2)
    php22, php22_n = pigeonhole_cnf(2, 2)
    return [
        {"name": "empty-formula", "cnf": (), "num_vars": 3, "expected": STATUS_SAT},
        {"name": "empty-clause", "cnf": ((),), "num_vars": 2, "expected": STATUS_UNSAT},
        {"name": "single-unit", "cnf": ((1,),), "num_vars": 1, "expected": STATUS_SAT},
        {"name": "contradictory-units", "cnf": ((1,), (-1,)), "num_vars": 1, "expected": STATUS_UNSAT},
        {"name": "unit-chain", "cnf": ((1,), (-1, 2), (-2, 3)), "num_vars": 3, "expected": STATUS_SAT},
        {"name": "unit-chain-conflict", "cnf": ((1,), (-1, 2), (-2,)), "num_vars": 2, "expected": STATUS_UNSAT},
        {"name": "all-combinations-2sat-unsat", "cnf": ((1, 2), (1, -2), (-1, 2), (-1, -2)), "num_vars": 2, "expected": STATUS_UNSAT},
        {"name": "pigeonhole-3-into-2", "cnf": php32, "num_vars": php32_n, "expected": STATUS_UNSAT},
        {"name": "pigeonhole-2-into-2", "cnf": php22, "num_vars": php22_n, "expected": STATUS_SAT},
        {"name": "random-3cnf-seed-0", "cnf": generate_random_3cnf(6, 12, seed=0), "num_vars": 6, "expected": None},
        {"name": "random-3cnf-seed-7", "cnf": generate_random_3cnf(6, 20, seed=7), "num_vars": 6, "expected": None},
        {"name": "random-3cnf-seed-42", "cnf": generate_random_3cnf(5, 10, seed=42), "num_vars": 5, "expected": None},
    ]


def run_benchmark(
    output_path: Optional[str] = None,
    *,
    seeds: Sequence[int] = (0, 1, 2),
    sizes: Sequence[Tuple[int, int]] = ((4, 8), (6, 16), (6, 24), (8, 24)),
    max_nodes: int = 200000,
) -> dict:
    """Run both solvers on seeded instances and optionally save JSON.

    The JSON records the actual solver outputs (status plus deterministic
    node/literal-check counters).  No API or network access is involved.
    """
    records: List[dict] = []
    for instance in seeded_instances():
        brute = brute_force_solve(instance["cnf"], instance["num_vars"], max_nodes=max_nodes)
        dpll = dpll_solve(instance["cnf"], instance["num_vars"], max_nodes=max_nodes)
        records.append({
            "name": instance["name"], "kind": "seeded", "num_vars": instance["num_vars"],
            "num_clauses": len(instance["cnf"]), "expected": instance["expected"],
            "brute_force": brute.to_dict(), "dpll": dpll.to_dict(),
        })
    for (n_vars, n_clauses) in sizes:
        for seed in seeds:
            cnf = generate_random_3cnf(n_vars, n_clauses, seed=seed)
            brute = brute_force_solve(cnf, n_vars, max_nodes=max_nodes)
            dpll = dpll_solve(cnf, n_vars, max_nodes=max_nodes)
            records.append({
                "name": f"random-3cnf-n{n_vars}-m{n_clauses}-seed{seed}", "kind": "random-3cnf",
                "num_vars": n_vars, "num_clauses": n_clauses, "seed": seed, "expected": None,
                "brute_force": brute.to_dict(), "dpll": dpll.to_dict(),
            })
    payload = {
        "description": "Deterministic SAT experiment counters (nodes and literal checks). "
                       "Counts are exact search-work counters, not timing-based complexity evidence.",
        "max_nodes": max_nodes,
        "results": records,
    }
    if output_path is not None:
        Path(output_path).write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Educational SAT experiments (stdlib only).")
    sub = parser.add_subparsers(dest="command")
    bench = sub.add_parser("bench", help="run the benchmark suite and save real results as JSON")
    bench.add_argument("--output", default="sat_bench_results.json", help="where to write results JSON")
    bench.add_argument("--max-nodes", type=int, default=200000)
    args = parser.parse_args(argv)
    if args.command == "bench":
        payload = run_benchmark(args.output, max_nodes=args.max_nodes)
        disagreements = 0
        for record in payload["results"]:
            b, d = record["brute_force"]["status"], record["dpll"]["status"]
            if b != "UNKNOWN" and d != "UNKNOWN" and b != d:
                disagreements += 1
        print(f"wrote {args.output}: {len(payload['results'])} instances, disagreements={disagreements}")
        return 0 if disagreements == 0 else 1
    parser.print_help()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
