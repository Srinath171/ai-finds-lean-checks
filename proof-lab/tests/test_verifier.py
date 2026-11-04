"""Verifier and catalog tests. No network, no real Lean required."""

import subprocess
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import prover


def theorem(tid="nat_add_comm"):
    return prover.get_theorem(tid)


class CatalogTests(unittest.TestCase):
    def test_catalog_has_15_unique_fixed_theorems(self):
        catalog = prover.load_catalog()
        self.assertEqual(len(catalog), 15)
        self.assertEqual(len({t.id for t in catalog}), 15)
        self.assertEqual(len({t.name for t in catalog}), 15)
        counts = {}
        for t in catalog:
            counts[t.category] = counts.get(t.category, 0) + 1
            self.assertTrue(t.statement.startswith(f"theorem {t.name} "))
        self.assertEqual(counts["decide"], 3)
        self.assertGreaterEqual(counts["nat"], 3)
        self.assertGreaterEqual(counts["list"], 2)
        self.assertGreaterEqual(counts["prop"], 2)

    def test_reference_lean_matches_catalog_and_is_all_sorry(self):
        catalog = prover.load_catalog()
        text = (prover.PROJECT_ROOT / "theorems.lean").read_text(encoding="utf-8")
        for t in catalog:
            self.assertIn(t.statement, text)
        self.assertEqual(text.count("sorry"), 15 + 1)  # +1 in the header warning
        # The reference file must never be a source of verified proofs.
        self.assertIn("NEVER considered verified", text)

    def test_binder_names(self):
        self.assertEqual(theorem("nat_add_comm").binder_names, ["a", "b"])
        self.assertEqual(theorem("prop_and_comm").binder_names, ["P", "Q"])
        self.assertEqual(theorem("decide_two_add_two").binder_names, [])


class ValidatorTests(unittest.TestCase):
    def test_accepts_catalog_style_proofs(self):
        good = {
            "nat_add_comm": "exact Nat.add_comm a b",
            "nat_add_zero": "exact Nat.add_zero n",
            "list_append_nil": "simp",
            "prop_and_comm": "intro h\nexact And.intro h.2 h.1",
            "prop_or_intro_left": "intro h\nexact Or.inl h",
            "decide_two_add_two": "decide",
        }
        for tid, body in good.items():
            with self.subTest(tid=tid):
                result = prover.validate_proof_body(body, theorem(tid))
                self.assertTrue(result.ok, result.reason)

    def test_rejects_dangerous_or_out_of_scope_bodies(self):
        bad = [
            "sorry",
            "exact sorry",
            "admit",
            "axiom hacked : Nat",
            "exact Nat.add_comm a b -- comment",
            "import Mathlib",
            "#print axioms nat_add_comm",
            "#eval 1",
            "theorem evil : True := trivial",
            "def evil : Nat := 1",
            'exact "string literal"',
            "native_decide",
            "run_tac IO.println 1",
            "elab \"x\" : tactic => trivial",
            "macro \"x\" : tactic => trivial",
            "syntax \"x\" : tactic",
            "exact \\u{61}dd_comm a b",
            "exact Foo.bar a b",
            "aesop",
            "exact Nat.add_comm a b\n-- trailing comment",
            "exact Nat.add_comm a b /* block */",
            "omega; sorry",
            "",
            "   ",
        ]
        for body in bad:
            with self.subTest(body=body):
                result = prover.validate_proof_body(body, theorem())
                self.assertFalse(result.ok, body)

    def test_rejects_statement_redefinition_and_unicode_identifiers(self):
        self.assertFalse(prover.validate_proof_body(
            "theorem nat_add_comm (a b : Nat) : a + b = b + a := by rfl",
            theorem()).ok)
        self.assertFalse(prover.validate_proof_body("exact ∀ x, x", theorem()).ok)

    def test_all_demo_fixture_proofs_pass_validator(self):
        catalog = prover.load_catalog()
        self.assertEqual(set(prover.DEMO_PROOFS), {t.id for t in catalog})
        for t in catalog:
            with self.subTest(tid=t.id):
                result = prover.validate_proof_body(prover.DEMO_PROOFS[t.id], t)
                self.assertTrue(result.ok, result.reason)


def make_runner(returncode=0, stdout="", stderr="", capture=None):
    def runner(command, cwd=None, env=None, timeout=None):
        if capture is not None:
            capture["command"] = command
            capture["env"] = env
            candidate = Path(command[-1])
            capture["source"] = candidate.read_text(encoding="utf-8")
        return subprocess.CompletedProcess(command, returncode, stdout, stderr)
    return runner


class CheckerTests(unittest.TestCase):
    def test_verified_only_with_understood_allowed_axioms(self):
        capture = {}
        result = prover.check_proof(
            theorem(), "exact Nat.add_comm a b",
            runner=make_runner(0, "'nat_add_comm' depends on axioms: [propext]", capture=capture),
        )
        self.assertTrue(result.verified)
        self.assertEqual(result.status, "verified")
        self.assertEqual(result.axioms, ["propext"])
        # The verifier fixed the statement and appended its own axioms check.
        self.assertIn("theorem nat_add_comm (a b : Nat) : a + b = b + a := by",
                      capture["source"])
        self.assertIn("#print axioms nat_add_comm", capture["source"])
        self.assertNotIn("import", capture["source"])

    def test_no_axioms_output_is_verified(self):
        result = prover.check_proof(
            theorem(), "exact Nat.add_comm a b",
            runner=make_runner(0, "'nat_add_comm' does not depend on any axioms"),
        )
        self.assertTrue(result.verified)
        self.assertEqual(result.axioms, [])

    def test_exit_zero_alone_is_never_verified(self):
        result = prover.check_proof(
            theorem(), "exact Nat.add_comm a b",
            runner=make_runner(0, "some unparseable lean chatter"),
        )
        self.assertFalse(result.verified)
        self.assertEqual(result.status, "checker_error")

    def test_sorry_ax_is_rejected_despite_exit_zero(self):
        result = prover.check_proof(
            theorem(), "exact Nat.add_comm a b",
            runner=make_runner(
                0, "'nat_add_comm' depends on axioms: [sorryAx]"),
        )
        self.assertFalse(result.verified)
        self.assertEqual(result.status, "axioms_rejected")

    def test_unknown_axiom_is_rejected(self):
        result = prover.check_proof(
            theorem(), "exact Nat.add_comm a b",
            runner=make_runner(
                0, "'nat_add_comm' depends on axioms: [propext, MyAxiom]"),
        )
        self.assertFalse(result.verified)
        self.assertEqual(result.status, "axioms_rejected")

    def test_nonzero_exit_is_invalid_proof(self):
        result = prover.check_proof(
            theorem("nat_add_comm"), "rfl",
            runner=make_runner(1, "", "error: type mismatch"),
        )
        self.assertFalse(result.verified)
        self.assertEqual(result.status, "invalid_proof")

    def test_false_theorem_attempt_is_not_verified(self):
        false_thm = prover.Theorem(
            id="false_test", name="false_test",
            statement="theorem false_test (a b : Nat) : a + b = b",
            category="nat",
        )
        result = prover.check_proof(
            false_thm, "rfl",
            runner=make_runner(1, "", "error: Eq.refl does not prove this"),
        )
        self.assertFalse(result.verified)
        self.assertNotEqual(result.status, "verified")

    def test_sorry_body_never_reaches_lean(self):
        called = []
        result = prover.check_proof(
            theorem(), "sorry", runner=make_runner(0, "", capture=None)
            if not called else None,
        )
        self.assertEqual(result.status, "syntax_rejected")
        self.assertFalse(result.verified)

    def test_timeout_is_reported_separately(self):
        def slow(command, cwd=None, env=None, timeout=None):
            raise subprocess.TimeoutExpired(command, timeout)
        result = prover.check_proof(
            theorem(), "exact Nat.add_comm a b", runner=slow)
        self.assertFalse(result.verified)
        self.assertEqual(result.status, "timeout")

    def test_tool_unavailable_without_lean_or_runner(self):
        import unittest.mock as mock
        with mock.patch.object(prover.shutil, "which", return_value=None), mock.patch.object(prover, "_elan_binary", return_value=None):
            result = prover.check_proof(theorem(), "exact Nat.add_comm a b")
        self.assertFalse(result.verified)
        self.assertEqual(result.status, "tool_unavailable")

    def test_candidate_cannot_change_statement_via_runner_capture(self):
        capture = {}
        result = prover.check_proof(
            theorem(), "exact Nat.add_comm b a",
            runner=make_runner(1, "", "error", capture=capture),
        )
        self.assertFalse(result.verified)
        self.assertIn("theorem nat_add_comm (a b : Nat) : a + b = b + a",
                      capture["source"])


class AxiomParserTests(unittest.TestCase):
    def test_parse_variants(self):
        self.assertEqual(
            prover.parse_axioms_output(
                "'x' depends on axioms: [propext, Quot.sound]", "x"),
            {"propext", "Quot.sound"})
        self.assertEqual(
            prover.parse_axioms_output("'x' does not depend on any axioms", "x"),
            set())
        self.assertIsNone(prover.parse_axioms_output("garbage", "x"))
        self.assertIsNone(prover.parse_axioms_output(
            "'other' depends on axioms: [propext]", "x"))


if __name__ == "__main__":
    unittest.main()
