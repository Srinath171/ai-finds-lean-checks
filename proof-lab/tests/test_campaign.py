import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from types import SimpleNamespace
from unittest import mock

from frontier import campaign as c


def candidate(name="new candidate", claim=False):
    return json.dumps(dict(precise_candidate=name, proof_attempt="Unproved derivation",
                          missing_lemma="Uniform verifier missing", falsifiable_test="Test n=3",
                          claims_full_solution=claim))


def answer(name="new candidate"):
    return {"text": candidate(name), "usage": {"input_tokens": 10, "output_tokens": 20}}


class FakeProcess:
    def __init__(self, output=b'{"result":"No proof; missing uniform verifier","total_cost_usd":0.03}', running=False):
        self.stdin, self.stdout, self.stderr = io.BytesIO(), io.BytesIO(output), io.BytesIO()
        self.running, self.returncode, self.killed = running, None if running else 0, False
    def poll(self):
        return None if self.running else self.returncode
    def wait(self, timeout=None):
        if self.running:
            raise subprocess.TimeoutExpired("claude", timeout)
        return self.returncode
    def kill(self):
        self.running, self.returncode, self.killed = False, -9, True


class CampaignTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="campaign-test-", dir=Path(__file__).parent)
        self.addCleanup(self.temp.cleanup)
        self.output = Path(self.temp.name)
        self.meta = mock.Mock(side_effect=lambda *a, **k: answer(str(self.meta.call_count)))
        self.critic = mock.Mock(return_value={"text": "Unverified: no uniform verifier", "usage": {}, "list_price_usd": 0.03})
        self.clock = 1000.0
        self.prints = mock.patch("builtins.print")
        self.prints.start()
        self.addCleanup(self.prints.stop)
    def run_work(self, **kwargs):
        defaults = dict(output_dir=self.output, meta_client=self.meta, claude_client=self.critic,
                        monotonic=lambda: self.clock, wall_time=lambda: self.clock)
        defaults.update(kwargs)
        return c.run_campaign(**defaults)
    def test_hard_caps_and_one_explicit_fable(self):
        fable = mock.Mock(return_value={"text": "UNVERIFIED: missing lemma", "usage": {}})
        result = self.run_work(use_fable=True, fable_client=fable)
        self.assertEqual(self.meta.call_count, 12)
        self.assertEqual(self.critic.call_count, 12)
        self.assertEqual(fable.call_count, 1)
        self.assertEqual(result["claude_list_price_ceiling_usd"], 24)
        self.assertEqual(result["status"], "NOT_SOLVED")
        self.assertEqual(result["claim_status"], "UNVERIFIED")
        saved = json.loads((self.output / "round-001.json").read_text(encoding="utf-8"))
        self.assertEqual(set(saved["prompts"]), {"meta", "claude", "fable"})
        self.assertEqual(saved["responses"]["meta"]["usage"]["output_tokens"], 20)
        self.assertLessEqual(len(saved["prompts"]["fable"].encode()), 32768)
    def test_default_never_calls_fable_or_resets_terminal_run(self):
        fable = mock.Mock(side_effect=AssertionError("must not call Fable"))
        first = self.run_work(max_rounds=1, fable_client=fable)
        second = self.run_work(fable_client=fable)
        self.assertEqual(first, second)
        self.assertEqual(self.meta.call_count, 1)
        fable.assert_not_called()
    def test_invalid_caps_fail_before_transport(self):
        for options in ({"hours": 8}, {"hours": float("nan")}, {"hours": -1}, {"max_rounds": 13},
                        {"max_rounds": True}, {"request_timeout": 601}):
            with self.subTest(options=options), self.assertRaises(ValueError):
                self.run_work(**options)
        self.meta.assert_not_called()
    def test_deadline_stops_before_critic(self):
        def model(*args, **kwargs):
            self.assertLessEqual(kwargs["timeout"], 1)
            self.clock += 2
            return answer()
        self.meta.side_effect = model
        result = self.run_work(hours=1/3600)
        self.assertEqual(result["reason"], "deadline")
        self.critic.assert_not_called()
    def test_stop_file_and_stale_lock_are_fail_closed(self):
        (self.output / "STOP").touch()
        self.assertEqual(self.run_work()["reason"], "stop_file")
        self.meta.assert_not_called()
        (self.output / "campaign.lock").touch()
        with self.assertRaises(FileExistsError):
            self.run_work()
    def test_duplicate_candidate_twice_stops(self):
        self.meta.side_effect = None
        self.meta.return_value = answer(" SAME  candidate ")
        result = self.run_work(use_claude=False)
        self.assertEqual(result["rounds_started"], 3)
        self.assertEqual(result["reason"], "repeated_candidate")
    def test_empty_malformed_and_error_repeat_stop(self):
        for bad in ("", "narrative only", '{"precise_candidate":"x"}'):
            with self.subTest(bad=bad), tempfile.TemporaryDirectory(dir=self.output) as folder:
                model = mock.Mock(return_value={"text": bad})
                result = self.run_work(output_dir=folder, meta_client=model)
                self.assertEqual(model.call_count, 2)
                self.assertEqual(result["reason"], "repeated_error_or_empty_result")
                self.assertEqual(result["status"], "NOT_SOLVED")
        with tempfile.TemporaryDirectory(dir=self.output) as folder:
            model = mock.Mock(side_effect=RuntimeError("secret-do-not-log"))
            self.run_work(output_dir=folder, meta_client=model)
            self.assertNotIn("secret-do-not-log", (Path(folder) / "round-001.json").read_text())
    def test_full_solution_claim_never_marked_solved(self):
        self.meta.side_effect = None
        self.meta.return_value = {"text": candidate(claim=True)}
        result = self.run_work()
        self.assertEqual(result["status"], "NEEDS_EXPERT_REVIEW")
        self.assertEqual(result["claim_status"], "UNVERIFIED")
        self.critic.assert_not_called()
        self.assertFalse(c._claims_solution("Unverified partial proposal"))
        self.assertTrue(c._claims_solution("P != NP proved"))
    def test_budget_refusal_stops_immediately(self):
        from budget import BudgetExceeded
        self.meta.side_effect = BudgetExceeded("No budget left")
        result = self.run_work()
        self.assertEqual(result["reason"], "budget_stop")
        self.assertEqual(self.meta.call_count, 1)
    def test_resume_preserves_deadline_and_counters(self):
        state = self.run_work(max_rounds=12)
        state.update(phase="RUNNING", rounds_started=11, claude_requests=11, fable_requests=1,
                     errors=0, deadline_epoch=1001)
        (self.output / "status.json").write_text(json.dumps(state), encoding="utf-8")
        fable = mock.Mock(side_effect=AssertionError("one Fable already used"))
        self.meta.reset_mock()
        self.critic.reset_mock()
        result = self.run_work(use_fable=True, fable_client=fable)
        self.assertEqual(result["deadline_epoch"], 1001)
        self.assertEqual(result["rounds_started"], 12)
        self.assertEqual(result["claude_requests"], 12)
        self.assertEqual(self.meta.call_count, 1)
        fable.assert_not_called()
    def test_interrupted_terminal_decision_stays_stopped(self):
        state = self.run_work(max_rounds=1)
        state.update(phase="RUNNING", status="NEEDS_EXPERT_REVIEW", max_rounds=12)
        (self.output / "status.json").write_text(json.dumps(state), encoding="utf-8")
        self.meta.reset_mock()
        resumed = self.run_work()
        self.assertEqual(resumed["status"], "NEEDS_EXPERT_REVIEW")
        self.assertEqual(resumed["phase"], "STOPPED")
        self.meta.assert_not_called()
        for key in ("errors", "duplicates"):
            state.update(status="NOT_SOLVED", phase="RUNNING", errors=0, duplicates=0)
            state[key] = 2
            (self.output / "status.json").write_text(json.dumps(state), encoding="utf-8")
            self.assertEqual(self.run_work()["phase"], "STOPPED")
            self.meta.assert_not_called()
    def test_escaped_full_solution_claim_stops(self):
        self.meta.side_effect = None
        self.meta.return_value = {"text": candidate(claim=True).replace("claims_full_solution", r"claims_\u0066ull_solution")}
        result = self.run_work()
        self.assertEqual(result["status"], "NEEDS_EXPERT_REVIEW")
        self.assertEqual(self.meta.call_count, 1)
    def test_fixed_process_worker_and_budget_refusal(self):
        with mock.patch.object(c, "_capture", return_value=answer()) as capture:
            c._provider_process("meta", c.SEED, 3)
            args, prompt, timeout = capture.call_args.args
            self.assertEqual(args[0], c.sys.executable)
            self.assertEqual(args[args.index("--worker")+1], "meta")
            self.assertEqual(timeout, 3)
            self.assertEqual(prompt, c.SEED)
        from budget import BudgetError
        with mock.patch.object(c, "_capture", return_value={"worker_error": "ApiError", "budget_error": True}), self.assertRaises(BudgetError):
            c._provider_process("meta", c.SEED, 3)
        with self.assertRaises(ValueError):
            c._provider_process("arbitrary", c.SEED, 3)
    def test_worker_entrypoint_uses_only_stdin_public_prompt(self):
        with mock.patch.object(c.sys, "stdin", SimpleNamespace(buffer=io.BytesIO(b"public math"))), mock.patch.object(c, "_meta", return_value=answer()) as meta:
            self.assertEqual(c.main(["--worker", "meta", "--request-timeout", "2"]), 0)
            meta.assert_called_once_with("public math", 2)
    def test_safe_api_error_categories_and_http_ranges(self):
        from prover import ApiError
        cases = [("MODEL_API_KEY is not set (environment or local .env)", "missing_key", None),
                 ("API request failed: secret-sentinel", "transport", None),
                 ("API HTTP 429: secret-sentinel", "transport", 429),
                 ("API response had an unexpected shape", "unexpected_shape", None),
                 ("API response content was not text", "content_type", None),
                 ("Spending ledger refused request: secret-sentinel", "ledger", None),
                 ("secret-sentinel", "unknown", None)]
        for text, category, code in cases:
            with self.subTest(category=category):
                metadata = c._safe_error_metadata(ApiError(text))
                self.assertEqual(metadata, {"category": category, "http_status": code})
                self.assertNotIn("secret-sentinel", json.dumps(metadata))
        for number in (99, 600, 1000):
            self.assertIsNone(c._safe_error_metadata(ApiError(f"API HTTP {number}: secret-sentinel"))["http_status"])
        for number in (100, 599):
            self.assertEqual(c._safe_error_metadata(ApiError(f"API HTTP {number}"))["http_status"], number)
    def test_error_metadata_handles_invalid_attributes_and_fable_key_config(self):
        error = RuntimeError("secret-sentinel")
        error.safe_error_category = {"untrusted": "secret-sentinel"}
        error.status = ["untrusted"]
        self.assertEqual(c._safe_error_metadata(error), {"category": "unknown", "http_status": None})
        from research_client import ResearchError
        error = ResearchError("Credential unavailable; secret-sentinel", status="configuration_error")
        self.assertEqual(c._safe_error_metadata(error), {"category": "missing_key", "http_status": None})
    def test_worker_error_protocol_excludes_body_and_secret(self):
        from prover import ApiError
        with mock.patch.object(c.sys, "stdin", SimpleNamespace(buffer=io.BytesIO(b"public math"))), \
             mock.patch.object(c, "_meta", side_effect=ApiError("API HTTP 502: secret-sentinel")), mock.patch("builtins.print") as printed:
            c.main(["--worker", "meta"])
        payload = json.loads(printed.call_args.args[0])
        self.assertEqual(payload["safe_error"], {"category": "transport", "http_status": 502})
        self.assertNotIn("secret-sentinel", json.dumps(payload))
        with mock.patch.object(c, "_capture", return_value=payload), self.assertRaises(c.ProviderWorkerError) as raised:
            c._provider_process("meta", c.SEED, 3)
        self.assertEqual(c._safe_error_metadata(raised.exception), payload["safe_error"])
    def test_safe_worker_metadata_persists_per_round(self):
        self.meta.side_effect = c.ProviderWorkerError({"category": "transport", "http_status": 503})
        self.run_work()
        saved = json.loads((self.output / "round-001.json").read_text(encoding="utf-8"))
        self.assertEqual(saved["error_metadata"], {"category": "transport", "http_status": 503})
        self.assertNotIn("secret", json.dumps(saved))
        invalid = c.ProviderWorkerError({"category": "secret-sentinel", "http_status": True})
        self.assertEqual(c._safe_error_metadata(invalid), {"category": "unknown", "http_status": None})
    def test_missing_or_corrupt_status_refuses_reset(self):
        (self.output / "round-001.json").write_text("{}")
        with self.assertRaises(ValueError):
            self.run_work()
        (self.output / "status.json").write_text('{"version":1}')
        with self.assertRaises(ValueError):
            self.run_work()
        self.meta.assert_not_called()
    def test_no_source_or_credentials_read_before_mock_transport(self):
        original = Path.open
        def guarded(path, mode="r", *args, **kwargs):
            if "r" in mode and not path.resolve().is_relative_to(self.output.resolve()):
                raise AssertionError("No reads outside campaign state")
            return original(path, mode, *args, **kwargs)
        with mock.patch.object(Path, "open", guarded):
            self.run_work(max_rounds=1)
    def test_parser_fences_and_rejections(self):
        self.assertEqual(c.parse_candidate("```json\n" + candidate() + "\n```")["missing_lemma"], "Uniform verifier missing")
        for value in (None, [], "x"*(c.MAX_TEXT+1), "[]", candidate().replace("false", '"false"')):
            with self.subTest(value=str(value)[:30]), self.assertRaises((ValueError, TypeError)):
                c.parse_candidate(value)
    def test_provider_wrappers_parameters_only_mocked(self):
        with mock.patch("prover.chat_completion", return_value=SimpleNamespace(content=candidate(), usage={}, model="muse-wonder-1.0")) as meta:
            c._meta(c.SEED, 7)
            self.assertEqual(meta.call_args.kwargs["max_tokens"], 16384)
            self.assertEqual(meta.call_args.kwargs["effort"], "max")
            self.assertEqual(meta.call_args.kwargs["timeout"], 7)
        with mock.patch("research_client.ask_public_math", return_value={}) as fable:
            c._fable(c.SEED, 8)
            self.assertEqual(fable.call_args.kwargs["max_tokens"], 8192)
            with self.assertRaises(ValueError):
                c._fable("a"*32769, 8)
            self.assertEqual(fable.call_count, 1)
    def test_claude_cli_tools_disabled_no_shell_no_api_env(self):
        process = FakeProcess()
        factory = mock.Mock(return_value=process)
        with mock.patch.dict(os.environ, {"ANTHROPIC_API_KEY": "never-pass", "MODEL_API_KEY": "never-pass"}):
            receipt = c.claude_critique("Public math only", popen=factory)
        args = factory.call_args.args[0]
        options = factory.call_args.kwargs
        self.assertIn("--tools=", args)
        self.assertIn("--safe-mode", args)
        self.assertIn("--strict-mcp-config", args)
        self.assertEqual(args[args.index("--max-budget-usd")+1], "2")
        self.assertFalse(options["shell"])
        self.assertEqual(options["cwd"], str(c.ROOT))
        self.assertNotIn("ANTHROPIC_API_KEY", options["env"])
        self.assertNotIn("MODEL_API_KEY", options["env"])
        self.assertEqual(receipt["list_price_usd"], .03)
        self.assertIn("informational", receipt["billing"])
    def test_claude_capture_size_and_timeout(self):
        with self.assertRaises(ValueError):
            c.claude_critique("math", popen=mock.Mock(return_value=FakeProcess(output=b"x"*100)), capture_limit=20)
        process = FakeProcess(running=True)
        with mock.patch.object(c.time, "monotonic", side_effect=[0, 2, 2]), self.assertRaises(TimeoutError):
            c.claude_critique("math", timeout=1, popen=mock.Mock(return_value=process))
        self.assertTrue(process.killed)


if __name__ == "__main__":
    unittest.main()
