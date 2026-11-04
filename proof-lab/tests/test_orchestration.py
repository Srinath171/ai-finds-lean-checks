"""Orchestration tests with fake model clients and fake checkers.

No network, no Lean, no API key. Fake clients return strings; fake
checkers return prover.VerificationResult values.
"""

import io
import json
import os
import sys
import tempfile
import unittest
import urllib.request
from contextlib import redirect_stdout
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import prover


def ok_checker(theorem, proof, timeout=None):
    return prover.VerificationResult(
        True, "verified", "'x' does not depend on any axioms", axioms=[])


class FakeClient:
    def __init__(self, bodies, usage=None):
        self.bodies = list(bodies)
        self.calls = []
        self.usage = usage or {"input_tokens": 10, "output_tokens": 5,
                               "total_tokens": 15, "reasoning_tokens": 2}

    def __call__(self, *, model, messages, max_tokens, effort, timeout):
        self.calls.append(messages)
        body = self.bodies.pop(0) if self.bodies else self.bodies_default
        return prover.ApiResult(content=body, usage=dict(self.usage), model=model)

    bodies_default = "simp"


class LoopTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.log = Path(self.tmp.name) / "runs.jsonl"

    def tearDown(self):
        self.tmp.cleanup()

    def test_retry_feeds_diagnostics_back_then_verifies(self):
        client = FakeClient(["sorry", "exact Nat.add_comm a b"])

        def checker2(theorem, proof, timeout=None):
            if proof.startswith("exact Nat.add_comm"):
                return ok_checker(theorem, proof)
            return prover.VerificationResult(
                False, "invalid_proof", "error: type mismatch XYZ")

        result = prover.prove_theorem(
            "nat_add_comm", client_fn=client, checker_fn=checker2,
            log_path=self.log, max_attempts=5)
        self.assertEqual(result["status"], "verified")
        self.assertTrue(result["verified"])
        self.assertEqual(result["attempt_count"], 2)
        second_prompt = client.calls[1][1]["content"]
        self.assertIn("type mismatch XYZ", second_prompt)  # diagnostics fed back
        self.assertEqual(result["usage_totals"]["reasoning_tokens"], 4)
        lines = self.log.read_text(encoding="utf-8").strip().splitlines()
        self.assertEqual(len(lines), 1)
        logged = json.loads(lines[0])
        self.assertEqual(logged["run_id"], result["run_id"])
        self.assertEqual(logged["status"], "verified")

    def test_sorry_injection_exhausts_as_invalid_not_verified(self):
        client = FakeClient(["sorry"] * 3)
        result = prover.prove_theorem(
            "nat_add_comm", client_fn=client,
            checker_fn=lambda th, pr, timeout=None: prover.VerificationResult(
                False, "syntax_rejected", "banned construct: sorry"),
            log_path=self.log, max_attempts=3)
        self.assertFalse(result["verified"])
        self.assertEqual(result["status"], "invalid_proof")
        self.assertEqual(result["attempt_count"], 3)

    def test_false_theorem_proof_never_verifies(self):
        client = FakeClient(["rfl", "rfl"])

        def lean_like(theorem, proof, timeout=None):
            # rfl does not prove a + b = b + a for variables.
            return prover.VerificationResult(
                False, "invalid_proof", "error: type mismatch")

        result = prover.prove_theorem(
            "nat_add_comm", client_fn=client, checker_fn=lean_like,
            log_path=self.log, max_attempts=2)
        self.assertFalse(result["verified"])
        self.assertEqual(result["status"], "invalid_proof")

    def test_api_error_is_distinct_and_stops(self):
        def client(**kwargs):
            raise prover.ApiError("API HTTP 500: boom")

        result = prover.prove_theorem(
            "nat_add_comm", client_fn=client, checker_fn=ok_checker,
            log_path=self.log)
        self.assertEqual(result["status"], "api_error")
        self.assertFalse(result["verified"])
        self.assertEqual(result["attempt_count"], 1)

    def test_tool_unavailable_is_distinct_and_stops(self):
        client = FakeClient(["simp", "simp"])
        result = prover.prove_theorem(
            "nat_add_comm", client_fn=client,
            checker_fn=lambda th, pr, timeout=None: prover.VerificationResult(
                False, "tool_unavailable", "lean not found"),
            log_path=self.log)
        self.assertEqual(result["status"], "tool_unavailable")
        self.assertEqual(result["attempt_count"], 1)

    def test_run_ids_are_unique_and_log_is_jsonl(self):
        client = FakeClient(["simp"])
        r1 = prover.prove_theorem("prop_id", client_fn=client,
                                  checker_fn=ok_checker, log_path=self.log)
        client2 = FakeClient(["simp"])
        r2 = prover.prove_theorem("prop_id", client_fn=client2,
                                  checker_fn=ok_checker, log_path=self.log)
        self.assertNotEqual(r1["run_id"], r2["run_id"])
        records = prover.read_run_logs(self.log)
        self.assertEqual(len(records), 2)
        summary = prover.summarize_logs(records)
        self.assertEqual(summary["verified_runs"], 2)
        self.assertEqual(summary["by_status"], {"verified": 2})

    def test_unknown_cost_without_rates(self):
        client = FakeClient(["simp"])
        result = prover.prove_theorem(
            "prop_id", client_fn=client, checker_fn=ok_checker,
            log_path=self.log)
        self.assertIsNone(result["cost_usd"])

    def test_budget_requires_rates_and_caps_spend(self):
        client = FakeClient(["simp"])
        with self.assertRaises(ValueError):
            prover.prove_theorem("prop_id", client_fn=client,
                                 checker_fn=ok_checker, log_path=self.log,
                                 budget_usd=1.0)
        big = FakeClient(["simp", "simp", "simp"], usage={
            "input_tokens": 1_000_000, "output_tokens": 1_000_000,
            "total_tokens": 2_000_000, "reasoning_tokens": None})
        result = prover.prove_theorem(
            "prop_id", client_fn=big,
            checker_fn=lambda th, pr, timeout=None: prover.VerificationResult(
                False, "invalid_proof", "nope"),
            log_path=self.log, budget_usd=1.0,
            input_rate_per_mtok=1.0, output_rate_per_mtok=1.0, max_attempts=5)
        self.assertEqual(result["status"], "budget_exceeded")
        self.assertEqual(result["attempt_count"], 1)
        self.assertEqual(result["cost_usd"], 2.0)

    def test_attempt_and_token_bounds_enforced(self):
        with self.assertRaises(ValueError):
            prover.prove_theorem("prop_id", max_attempts=6, log_path=self.log)
        with self.assertRaises(ValueError):
            prover.prove_theorem("prop_id", max_tokens=99999, log_path=self.log)
        with self.assertRaises(ValueError):
            prover.prove_theorem("prop_id", model="not-a-model", log_path=self.log)
        with self.assertRaises(ValueError):
            prover.prove_theorem("no_such_theorem", log_path=self.log)


class ApiClientTests(unittest.TestCase):
    def test_chat_completion_parses_content_and_reasoning_tokens(self):
        captured = {}

        class FakeResponse:
            def __enter__(self):
                return self

            def __exit__(self, *args):
                return False

            def read(self, n=-1):
                return json.dumps({
                    "choices": [{"message": {"content": "simp"}}],
                    "usage": {"prompt_tokens": 11, "completion_tokens": 7,
                              "total_tokens": 18,
                              "completion_tokens_details":
                                  {"reasoning_tokens": 3}},
                }).encode()

        def opener(request, timeout=None):
            captured["url"] = request.full_url
            captured["auth"] = request.get_header("Authorization")
            captured["body"] = json.loads(request.data.decode())
            return FakeResponse()

        with mock.patch.dict(os.environ, {"MODEL_API_KEY": "test-dummy-key"}):
            result = prover.chat_completion(
                model="muse-spark-1.3",
                messages=[{"role": "user", "content": "x"}],
                opener=opener)
        self.assertEqual(result.content, "simp")
        self.assertEqual(result.usage["reasoning_tokens"], 3)
        self.assertEqual(captured["url"], prover.API_URL)
        self.assertEqual(captured["url"],
                         "https://api.meta.ai/v1/chat/completions")
        self.assertEqual(captured["body"]["model"], "muse-spark-1.3")
        self.assertNotIn("test-dummy-key", json.dumps(captured["body"]))

    def test_chat_completion_rejects_bad_model_and_missing_key(self):
        with self.assertRaises(prover.ApiError):
            prover.chat_completion(model="gpt-x", messages=[], api_key="k")
        with mock.patch.object(prover, "get_api_key", return_value=None):
            with self.assertRaises(prover.ApiError):
                prover.chat_completion(
                    model="muse-spark-1.3", messages=[], api_key=None,
                    opener=lambda *a, **k: None)

    def test_api_key_from_dotenv_file_in_temp_dir(self):
        with tempfile.TemporaryDirectory() as tmp:
            env_file = Path(tmp) / ".env"
            env_file.write_text("MODEL_API_KEY=test-dummy-from-file\n",
                                encoding="utf-8")
            with mock.patch.dict(os.environ, {}, clear=True):
                self.assertEqual(
                    prover.get_api_key(dotenv_path=env_file),
                    "test-dummy-from-file")

    def test_extract_proof_body_strips_fences(self):
        self.assertEqual(prover.extract_proof_body("```lean\nsimp\n```"), "simp")
        self.assertEqual(prover.extract_proof_body("  simp "), "simp")

    def test_sanitized_env_drops_secrets(self):
        with mock.patch.dict(os.environ, {
                "MODEL_API_KEY": "x", "MY_SECRET": "y",
                "SOME_TOKEN": "z", "PATH": "p", "PLAIN": "v"}):
            env = prover._sanitized_env()
        self.assertNotIn("MODEL_API_KEY", env)
        self.assertNotIn("MY_SECRET", env)
        self.assertNotIn("SOME_TOKEN", env)
        self.assertEqual(env.get("PLAIN"), "v")


class CliTests(unittest.TestCase):
    def test_list_command(self):
        out = io.StringIO()
        with redirect_stdout(out):
            code = prover.main(["list"])
        self.assertEqual(code, 0)
        self.assertIn("nat_add_comm", out.getvalue())
        self.assertIn("decide_two_mem_list", out.getvalue())

    def test_check_command_rejects_sorry_without_lean(self):
        out = io.StringIO()
        with redirect_stdout(out):
            code = prover.main(["check", "nat_add_comm", "--proof", "sorry"])
        self.assertEqual(code, 1)
        self.assertIn("syntax_rejected", out.getvalue())
        self.assertIn("NOT VERIFIED", out.getvalue())


if __name__ == "__main__":
    unittest.main()
