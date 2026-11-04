"""Offline research-client checks: fake transport, dummy key, temporary ledger."""
import contextlib
from decimal import Decimal
import io
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
import urllib.error
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import research_client as client
from budget import BudgetLedger


class ResearchClientTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.ledger_path = self.root / "spending.json"
        self.patch_path = mock.patch.object(client, "SPENDING_LEDGER_PATH", self.ledger_path)
        self.patch_key = mock.patch.object(client, "_read_api_key", return_value="offline-test-key")
        self.patch_path.start()
        self.patch_key.start()

    def tearDown(self):
        self.patch_key.stop()
        self.patch_path.stop()
        self.tmp.cleanup()

    def status(self):
        return BudgetLedger(self.ledger_path).status()

    @staticmethod
    def message(**updates):
        result = {"type": "message", "model": client.MODEL,
                  "content": [{"type": "text", "text": "Public mathematical argument."}],
                  "stop_reason": "end_turn",
                  "usage": {"input_tokens": 20, "output_tokens": 30,
                            "cache_creation_input_tokens": 0, "cache_read_input_tokens": 0}}
        result.update(updates)
        return result

    @classmethod
    def response(cls, **updates):
        return io.BytesIO(json.dumps(cls.message(**updates)).encode("utf-8"))

    def call(self, **kwargs):
        return client.ask_public_math("Prove that zero plus n equals n.", max_tokens=100, **kwargs)

    def test_reservation_precedes_fixed_https_request_and_usage_settles(self):
        def transport(request, *, timeout):
            self.assertEqual(request.full_url, "https://api.anthropic.com/v1/messages")
            self.assertEqual(request.method, "POST")
            self.assertEqual(request.get_header("X-api-key"), "offline-test-key")
            self.assertEqual(request.get_header("Anthropic-version"), "2023-06-01")
            body = json.loads(request.data)
            self.assertEqual(body, {"model": "claude-fable-5", "max_tokens": 100,
                                   "output_config": {"effort": "max"},
                                   "messages": [{"role": "user", "content": "Prove that zero plus n equals n."}]})
            status = self.status()
            self.assertEqual(status["providers"]["claude"]["pending_count"], 1)
            self.assertEqual(status["providers"]["claude"]["cap_usd"], "40")
            self.assertEqual(status["providers"]["claude"]["external_hold_usd"], "1")
            self.assertEqual(status["providers"]["meta"]["external_hold_usd"], "25")
            expected = (Decimal(len(request.data) + 4096) * 10 + Decimal(100) * 50) / 1_000_000
            self.assertEqual(Decimal(status["reservations"][0]["reserved_usd"]), expected)
            self.assertEqual(timeout, 180)
            return self.response()
        with mock.patch.object(client, "_open_request", side_effect=transport):
            result = self.call()
        self.assertFalse(result["incomplete"])
        self.assertEqual(result["text"], "Public mathematical argument.")
        self.assertEqual(result["cost_usd"], "0.0017")
        self.assertEqual(result["usage_status"], "settled")
        self.assertEqual(self.status()["providers"]["claude"]["settled_count"], 1)
        self.assertNotIn("offline-test-key", self.ledger_path.read_text())

    def test_existing_caps_and_external_holds_are_preserved(self):
        BudgetLedger(self.ledger_path, caps={"meta": 30, "claude": 2},
                     initial_holds={"meta": 12, "claude": 1})
        with mock.patch.object(client, "_open_request", return_value=self.response()):
            self.call()
        providers = self.status()["providers"]
        self.assertEqual(providers["meta"]["cap_usd"], "30")
        self.assertEqual(providers["meta"]["external_hold_usd"], "12")
        self.assertEqual(providers["claude"]["cap_usd"], "2")

    def test_cap_failure_never_enters_transport(self):
        BudgetLedger(self.ledger_path, initial_holds={"meta": 25, "claude": 40})
        with mock.patch.object(client, "_open_request") as transport:
            with self.assertRaises(client.ResearchError) as caught:
                self.call()
            self.assertEqual(caught.exception.status, "budget_error")
            transport.assert_not_called()

    def test_existing_cap_above_authorized_40_dollars_is_rejected(self):
        BudgetLedger(self.ledger_path, caps={"meta": 125, "claude": 100})
        with mock.patch.object(client, "_open_request") as transport:
            with self.assertRaises(client.ResearchError) as caught:
                self.call()
            self.assertEqual(caught.exception.status, "budget_error")
            transport.assert_not_called()
        self.assertEqual(self.status()["providers"]["claude"]["pending_count"], 0)

    def test_maximum_output_budget_includes_thinking_and_returns_incomplete(self):
        data = self.message(content=[{"type": "thinking", "thinking": "PRIVATE HIDDEN REASONING"}],
                            stop_reason="max_tokens", usage={"input_tokens": 1, "output_tokens": 65536})
        with mock.patch.object(client, "_open_request", return_value=io.BytesIO(json.dumps(data).encode())) as transport:
            result = client.ask_public_math("Public conjecture", max_tokens=65536)
        self.assertEqual(json.loads(transport.call_args.args[0].data)["max_tokens"], 65536)
        self.assertTrue(result["incomplete"])
        self.assertEqual(result["text"], "")
        self.assertNotIn("PRIVATE HIDDEN", json.dumps(result))
        self.assertEqual(result["cost_usd"], "3.27681")
        self.assertEqual(result["usage_status"], "settled")

    def test_only_visible_text_blocks_are_returned(self):
        content = [{"type": "thinking", "thinking": "do not return"},
                   {"type": "redacted_thinking", "data": "do not return either"},
                   {"type": "text", "text": "First"}, {"type": "text", "text": "Second"}]
        with mock.patch.object(client, "_open_request", return_value=self.response(content=content)):
            result = self.call()
        self.assertEqual(result["text"], "First\nSecond")
        self.assertNotIn("do not return", json.dumps(result))

    def test_missing_or_invalid_usage_retains_full_reservation(self):
        bad_usages = [None, {}, {"input_tokens": True, "output_tokens": 2},
                      {"input_tokens": 1, "output_tokens": -1},
                      {"input_tokens": 1.5, "output_tokens": 2},
                      {"input_tokens": 1, "output_tokens": 2, "cache_read_input_tokens": True},
                      {"input_tokens": 1, "output_tokens": 2, "cache_creation_input_tokens": -1},
                      {"input_tokens": 1, "output_tokens": 2, "cache_creation_input_tokens": 3},
                      {"input_tokens": 1, "output_tokens": 2, "cache_creation": None}]
        for usage in bad_usages:
            with self.subTest(usage=usage):
                with mock.patch.object(client, "_open_request", return_value=self.response(usage=usage)):
                    result = self.call()
                self.assertEqual(result["usage_status"], "pending")
                self.assertIsNone(result["cost_usd"])
                self.assertIsNone(result["usage"])
        self.assertEqual(self.status()["providers"]["claude"]["pending_count"], len(bad_usages))

    def test_explicit_cache_creation_and_reads_are_priced(self):
        usage = {"input_tokens": 20, "output_tokens": 30, "cache_creation_input_tokens": 9,
                 "cache_read_input_tokens": 11,
                 "cache_creation": {"ephemeral_5m_input_tokens": 4, "ephemeral_1h_input_tokens": 5}}
        with mock.patch.object(client, "_open_request", return_value=self.response(usage=usage)):
            result = self.call()
        self.assertEqual(Decimal(result["cost_usd"]), Decimal("0.001861"))
        self.assertEqual(result["usage"]["ephemeral_1h_input_tokens"], 5)

    def test_cached_breakdown_mismatch_remains_pending(self):
        usage = {"input_tokens": 1, "output_tokens": 1, "cache_creation_input_tokens": 3,
                 "cache_creation": {"ephemeral_5m_input_tokens": 2, "ephemeral_1h_input_tokens": 2}}
        with mock.patch.object(client, "_open_request", return_value=self.response(usage=usage)):
            result = self.call()
        self.assertEqual(result["usage_status"], "pending")

    def test_transport_errors_are_sanitized_and_pending(self):
        with mock.patch.object(client, "_open_request", side_effect=urllib.error.URLError("offline-test-key")):
            with self.assertRaises(client.ResearchError) as caught:
                self.call()
        self.assertEqual(caught.exception.status, "transport_error")
        self.assertNotIn("offline-test-key", json.dumps(caught.exception.as_dict()))
        self.assertEqual(self.status()["providers"]["claude"]["pending_count"], 1)

    def test_http_errors_expose_only_status(self):
        error = urllib.error.HTTPError(client.API_URL, 401, "offline-test-key", {}, io.BytesIO(b"offline-test-key"))
        with mock.patch.object(client, "_open_request", side_effect=error):
            with self.assertRaises(client.ResearchError) as caught:
                self.call()
        result = caught.exception.as_dict()
        self.assertEqual(result["http_status"], 401)
        self.assertEqual(result["status"], "http_error")
        self.assertNotIn("offline-test-key", json.dumps(result))
        self.assertEqual(self.status()["providers"]["claude"]["pending_count"], 1)

    def test_oversized_response_retains_reservation(self):
        with mock.patch.object(client, "MAX_RESPONSE_BYTES", 12):
            with mock.patch.object(client, "_open_request", return_value=io.BytesIO(b"x" * 13)):
                with self.assertRaises(client.ResearchError) as caught:
                    self.call()
        self.assertEqual(caught.exception.status, "invalid_response")
        self.assertEqual(self.status()["providers"]["claude"]["pending_count"], 1)

    def test_invalid_duplicate_nonfinite_and_unexpected_model_responses_are_rejected(self):
        payloads = [b"not JSON", b'{"type":"message","type":"message"}',
                    b'{"amount":NaN}', json.dumps(self.message(model="claude-other")).encode(),
                    json.dumps(self.message(content=[{"type": "text", "text": 5}])).encode()]
        for payload in payloads:
            with self.subTest(payload=payload[:50]):
                with mock.patch.object(client, "_open_request", return_value=io.BytesIO(payload)):
                    with self.assertRaises(client.ResearchError) as caught:
                        self.call()
                self.assertEqual(caught.exception.status, "invalid_response")
        self.assertEqual(self.status()["providers"]["claude"]["pending_count"], len(payloads))

    def test_invalid_inputs_do_not_load_key_or_enter_transport(self):
        self.patch_key.stop()
        with mock.patch.object(client, "_read_api_key") as key_reader:
            with mock.patch.object(client, "_open_request") as transport:
                for tokens in (True, 0, -1, 65537, 1.5):
                    with self.assertRaises(client.ResearchError):
                        client.ask_public_math("Public math", max_tokens=tokens)
                for timeout in (True, 0, -1, float("inf"), float("nan")):
                    with self.assertRaises(client.ResearchError):
                        client.ask_public_math("Public math", timeout=timeout)
                for prompt in ("", " ", None, "\ud800"):
                    with self.assertRaises(client.ResearchError):
                        client.ask_public_math(prompt)
                key_reader.assert_not_called()
                transport.assert_not_called()
        self.patch_key.start()
        self.assertFalse(self.ledger_path.exists())

    def test_missing_credential_never_reserves_or_transmits(self):
        with mock.patch.object(client, "_read_api_key", side_effect=client.ResearchError("Missing credential", status="configuration_error")):
            with mock.patch.object(client, "_open_request") as transport:
                with self.assertRaises(client.ResearchError):
                    self.call()
                transport.assert_not_called()
        self.assertFalse(self.ledger_path.exists())

    def test_credential_loader_uses_only_runtime_env_then_designated_env(self):
        self.patch_key.stop()
        env_path = self.root / "dummy.env"
        env_path.write_text('UNRELATED=ignored\nANTHROPIC_API_KEY="offline-file-placeholder"\n')
        try:
            with mock.patch.object(client, "ENV_PATH", env_path):
                with mock.patch.dict(os.environ, {"ANTHROPIC_API_KEY": "offline-env-placeholder"}):
                    self.assertEqual(client._read_api_key(), "offline-env-placeholder")
                with mock.patch.dict(os.environ, {"ANTHROPIC_API_KEY": ""}):
                    self.assertEqual(client._read_api_key(), "offline-file-placeholder")
        finally:
            self.patch_key.start()

    def test_measured_overrun_is_recorded_and_stops_caller(self):
        usage = {"input_tokens": 100000, "output_tokens": 1}
        with mock.patch.object(client, "_open_request", return_value=self.response(usage=usage)):
            with self.assertRaises(client.ResearchError) as caught:
                self.call()
        self.assertEqual(caught.exception.status, "budget_error")
        row = self.status()["reservations"][0]
        self.assertEqual(row["status"], "settled")
        self.assertEqual(Decimal(row["actual_usd"]), Decimal("1.00005"))

    def test_redirect_handler_never_forwards_credentials(self):
        handler = client._NoRedirect()
        self.assertIsNone(handler.redirect_request(None, None, 302, "redirect", {}, "https://example.test"))

    def test_cli_sends_only_explicit_prompt_and_saves_json(self):
        prompt = self.root / "public-math.txt"
        output = self.root / "result.json"
        prompt.write_text("Find a counterexample to this public claim.", encoding="utf-8")
        with mock.patch.object(client, "ask_public_math", return_value={"ok": True, "text": "candidate", "incomplete": False, "usage_status": "settled"}) as ask:
            with contextlib.redirect_stdout(io.StringIO()):
                exit_code = client.main(["--prompt-file", str(prompt), "--output", str(output), "--max-tokens", "4096"])
        self.assertEqual(exit_code, 0)
        ask.assert_called_once_with("Find a counterexample to this public claim.", 4096, 180)
        self.assertEqual(json.loads(output.read_text())["text"], "candidate")

    def test_cli_refuses_env_files_before_read_or_request(self):
        with mock.patch.object(client, "ask_public_math") as ask:
            with contextlib.redirect_stdout(io.StringIO()):
                code = client.main(["--prompt-file", str(self.root / ".env"), "--output", str(self.root / "result.json")])
        self.assertEqual(code, 1)
        ask.assert_not_called()
        self.assertEqual(json.loads((self.root / "result.json").read_text())["status"], "invalid_request")

    def test_cli_unsafe_output_never_overwrites_prompt_credentials_or_ledger(self):
        prompt = self.root / "public.txt"
        env_file = self.root / ".env"
        prompt.write_bytes(b"Original public prompt")
        env_file.write_bytes(b"OFFLINE DUMMY ONLY")
        self.ledger_path.write_bytes(b"Original accounting")
        protected = (prompt, env_file, self.ledger_path,
                     self.ledger_path.with_name(self.ledger_path.name + ".lock"))
        with mock.patch.object(client, "ENV_PATH", env_file):
            with mock.patch.object(client, "ask_public_math") as ask:
                for target in protected:
                    with self.subTest(target=target.name):
                        with contextlib.redirect_stderr(io.StringIO()):
                            code = client.main(["--prompt-file", str(prompt), "--output", str(target)])
                        self.assertEqual(code, 2)
                ask.assert_not_called()
        self.assertEqual(prompt.read_bytes(), b"Original public prompt")
        self.assertEqual(env_file.read_bytes(), b"OFFLINE DUMMY ONLY")
        self.assertEqual(self.ledger_path.read_bytes(), b"Original accounting")

    def test_cli_output_hardlink_to_prompt_is_rejected(self):
        prompt = self.root / "public.txt"
        alias = self.root / "alias.json"
        prompt.write_bytes(b"Original public prompt")
        try:
            os.link(prompt, alias)
        except OSError:
            self.skipTest("filesystem does not support hard links")
        with mock.patch.object(client, "ask_public_math") as ask:
            with contextlib.redirect_stderr(io.StringIO()):
                code = client.main(["--prompt-file", str(prompt), "--output", str(alias)])
            ask.assert_not_called()
        self.assertEqual(code, 2)
        self.assertEqual(prompt.read_bytes(), b"Original public prompt")


if __name__ == "__main__":
    unittest.main()
