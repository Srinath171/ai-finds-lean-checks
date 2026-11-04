"""Independent tests for sat_lab.

Oracle strategy (independent of the solvers):
  * exhaustive enumeration uses this file's own satisfaction predicate
    (``t_satisfies``) written directly from the definition, and compares
    against both solvers on every formula over n=2 variables, plus seeded
    random 3-CNF instances with n <= 6;
  * malformed formulas/assignments must be rejected (exception or False),
    never silently accepted.
Run with:  .venv\\Scripts\\python.exe -m pytest tests/test_sat_lab.py
       or: .venv\\Scripts\\python.exe -m unittest tests.test_sat_lab -v
"""
import itertools
import json
import random
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from sat_lab import (  # noqa: E402
    STATUS_SAT,
    STATUS_UNSAT,
    STATUS_UNKNOWN,
    CNFValidationError,
    brute_force_solve,
    dpll_solve,
    generate_random_3cnf,
    pigeonhole_cnf,
    seeded_instances,
    validate_assignment,
    validate_cnf,
    verify_assignment,
)


def t_satisfies(cnf, assignment):
    """Test-local definition: every clause has a literally-true literal."""
    for clause in cnf:
        ok = False
        for lit in clause:
            v = assignment[abs(lit)]
            if (lit > 0 and v is True) or (lit < 0 and v is False):
                ok = True
        if not ok:
            return False
    return True


def t_brute_status(cnf, num_vars):
    """Test-local exhaustive oracle over all 2**num_vars assignments."""
    for values in itertools.product((False, True), repeat=num_vars):
        assignment = {i + 1: values[i] for i in range(num_vars)}
        if t_satisfies(cnf, assignment):
            return STATUS_SAT, assignment
    return STATUS_UNSAT, None


def all_clauses(num_vars):
    """All clauses using each variable absent / positive / negative (3^n)."""
    clauses = []
    for choices in itertools.product((0, 1, -1), repeat=num_vars):
        clause = tuple(sign * (i + 1) for i, sign in enumerate(choices) if sign != 0)
        clauses.append(clause)
    return clauses


class TestExhaustiveSmall(unittest.TestCase):
    def test_all_formulas_n2_match_oracle(self):
        clauses = all_clauses(2)
        self.assertEqual(len(clauses), 9)
        checked = 0
        for r in range(len(clauses) + 1):
            for subset in itertools.combinations(clauses, r):
                cnf = tuple(subset)
                expected, model = t_brute_status(cnf, 2)
                for solver in (brute_force_solve, dpll_solve):
                    res = solver(cnf, 2)
                    self.assertEqual(res.status, expected, f"{solver.__name__} {cnf}")
                    if expected == STATUS_SAT:
                        self.assertIsNotNone(res.assignment)
                        self.assertTrue(t_satisfies(cnf, res.assignment))
                        self.assertTrue(verify_assignment(cnf, res.assignment, 2))
                checked += 1
        self.assertEqual(checked, 512)

    def test_all_formulas_up_to_3_clauses_n3(self):
        clauses = all_clauses(3)
        for r in range(4):
            for subset in itertools.combinations(clauses, r):
                cnf = tuple(subset)
                expected, _ = t_brute_status(cnf, 3)
                for solver in (brute_force_solve, dpll_solve):
                    res = solver(cnf, 3)
                    self.assertEqual(res.status, expected, f"{solver.__name__} {cnf}")
                    if res.status == STATUS_SAT:
                        self.assertTrue(verify_assignment(cnf, res.assignment, 3))

    def test_random_3cnf_small_crosscheck(self):
        for seed in range(10):
            for n_vars, n_clauses in ((4, 8), (5, 14), (6, 18), (6, 26)):
                cnf = generate_random_3cnf(n_vars, n_clauses, seed=seed)
                expected, _ = t_brute_status(cnf, n_vars)
                for solver in (brute_force_solve, dpll_solve):
                    res = solver(cnf, n_vars)
                    self.assertEqual(res.status, expected, f"{solver.__name__} seed={seed} {cnf}")
                    if res.status == STATUS_SAT:
                        self.assertTrue(verify_assignment(cnf, res.assignment, n_vars))

    def test_seeded_instances(self):
        for inst in seeded_instances():
            cnf, n = inst["cnf"], inst["num_vars"]
            self.assertLessEqual(n, 6) if inst["expected"] is not None else None
            expected_oracle, _ = t_brute_status(cnf, n)
            if inst["expected"] is not None:
                self.assertEqual(inst["expected"], expected_oracle, inst["name"])
            for solver in (brute_force_solve, dpll_solve):
                res = solver(cnf, n)
                self.assertEqual(res.status, expected_oracle, f"{inst['name']} {solver.__name__}")
                if res.status == STATUS_SAT:
                    self.assertTrue(verify_assignment(cnf, res.assignment, n))

    def test_pigeonhole_known_status(self):
        for (p, h, expected) in ((2, 2, STATUS_SAT), (3, 2, STATUS_UNSAT), (4, 3, STATUS_UNSAT)):
            cnf, n = pigeonhole_cnf(p, h)
            oracle, _ = t_brute_status(cnf, n) if n <= 12 else (expected, None)
            self.assertEqual(oracle, expected)
            self.assertEqual(brute_force_solve(cnf, n).status, expected)
            self.assertEqual(dpll_solve(cnf, n).status, expected)


class TestVerifierAndValidation(unittest.TestCase):
    def test_verifier_direct_cases(self):
        cnf = ((1, -2), (2, 3))
        self.assertTrue(verify_assignment(cnf, {1: True, 2: False, 3: True}, 3))
        self.assertFalse(verify_assignment(cnf, {1: False, 2: False, 3: False}, 3))
        self.assertTrue(verify_assignment((), {1: False}, 1))          # empty formula
        self.assertFalse(verify_assignment(((),), {1: True}, 1))       # empty clause
        self.assertTrue(verify_assignment(((1,),), [True], 1))         # sequence form
        self.assertFalse(verify_assignment(((1,),), [False], 1))

    def test_corrupted_assignments_rejected(self):
        cnf = ((1,), (-1, 2))
        good = {1: True, 2: True}
        self.assertTrue(verify_assignment(cnf, good, 2))
        # Flipping a variable the formula forces breaks satisfaction.
        self.assertFalse(verify_assignment(cnf, {1: False, 2: True}, 2))
        # Malformed assignments raise, never silently pass.
        for bad in ({1: True}, {1: True, 2: True, 3: False}, {1: True, 2: 1},
                    {1: True, 2: "yes"}, [True], [True, 1], "True", 42, None):
            with self.assertRaises(CNFValidationError, msg=f"assignment={bad!r}"):
                verify_assignment(cnf, bad, 2)
        with self.assertRaises(CNFValidationError):
            validate_assignment({0: True, 1: True}, 2)

    def test_corrupted_formulas_rejected(self):
        for bad in (((0,),), ((True,),), ((1.5,),), (("1",),), ((3,),), "((1,),)",
                    (1, 2), ((1, None),), None, 7):
            with self.assertRaises((CNFValidationError, TypeError), msg=f"cnf={bad!r}"):
                validate_cnf(bad, 2)
            with self.assertRaises((CNFValidationError, TypeError), msg=f"solver cnf={bad!r}"):
                brute_force_solve(bad, 2)
        with self.assertRaises(CNFValidationError):
            dpll_solve(((5,),), 2)
        # A satisfying assignment smuggled past a corrupted formula still fails.
        with self.assertRaises(CNFValidationError):
            verify_assignment(((0,),), {1: True}, 1)

    def test_solvers_never_certify_bad_model(self):
        # Every SAT answer on random instances must pass the verifier; flip
        # each returned model on a unit-forcing formula and it must fail.
        cnf = ((1,), (-1, 2), (-2, 3))
        for solver in (brute_force_solve, dpll_solve):
            res = solver(cnf, 3)
            self.assertEqual(res.status, STATUS_SAT)
            self.assertTrue(verify_assignment(cnf, res.assignment, 3))
            broken = dict(res.assignment)
            broken[1] = not broken[1]
            self.assertFalse(verify_assignment(cnf, broken, 3))


class TestCapsDeterminismAndBench(unittest.TestCase):
    def test_node_cap_gives_unknown_never_unsat(self):
        cnf = ((1, 2), (1, -2), (-1, 2), (-1, -2))  # UNSAT, needs full search
        for solver in (brute_force_solve, dpll_solve):
            for cap in (0, 1, 2):
                res = solver(cnf, 2, max_nodes=cap)
                self.assertEqual(res.status, STATUS_UNKNOWN, f"{solver.__name__} cap={cap}")
                self.assertNotEqual(res.status, STATUS_UNSAT)
        sat_cnf = generate_random_3cnf(6, 20, seed=3)
        for solver in (brute_force_solve, dpll_solve):
            res = solver(sat_cnf, 6, max_nodes=1)
            self.assertIn(res.status, (STATUS_SAT, STATUS_UNKNOWN))

    def test_deterministic_counters(self):
        cnf = generate_random_3cnf(6, 22, seed=11)
        for solver in (brute_force_solve, dpll_solve):
            a = solver(cnf, 6)
            b = solver(cnf, 6)
            self.assertEqual((a.status, a.assignment), (b.status, b.assignment))
            self.assertEqual(a.stats, b.stats)
            self.assertGreater(a.stats.nodes, 0)
            self.assertGreater(a.stats.literal_checks, 0)
        self.assertEqual(generate_random_3cnf(5, 9, seed=5), generate_random_3cnf(5, 9, seed=5))
        self.assertNotEqual(generate_random_3cnf(5, 9, seed=5), generate_random_3cnf(5, 9, seed=6))

    def test_bench_cli_writes_real_json(self):
        root = Path(__file__).resolve().parent.parent
        with tempfile.TemporaryDirectory(dir=root) as tmp:
            out = Path(tmp) / "bench.json"
            proc = subprocess.run(
                [sys.executable, "sat_lab.py", "bench", "--output", str(out)],
                cwd=root, capture_output=True, text=True, timeout=120,
            )
            self.assertEqual(proc.returncode, 0, proc.stderr)
            payload = json.loads(out.read_text(encoding="utf-8"))
        self.assertGreater(len(payload["results"]), 0)
        for record in payload["results"]:
            for algo in ("brute_force", "dpll"):
                self.assertIn(record[algo]["status"], (STATUS_SAT, STATUS_UNSAT, STATUS_UNKNOWN))
                self.assertGreaterEqual(record[algo]["stats"]["nodes"], 0)
                self.assertGreaterEqual(record[algo]["stats"]["literal_checks"], 0)
            b, d = record["brute_force"]["status"], record["dpll"]["status"]
            if STATUS_UNKNOWN not in (b, d):
                self.assertEqual(b, d, record["name"])


if __name__ == "__main__":
    unittest.main()
