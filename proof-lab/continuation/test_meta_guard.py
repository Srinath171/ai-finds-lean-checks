"""Offline continuation guards: fake keys, fake ledger, mock transport only."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock
from budget import BudgetLedger, BudgetError
from frontier import background_meta as old
from hour2 import phase_guard as old_phase
from continuation import meta_guard as guard


class Clock:
    def __init__(self):
        self.now = 1900000000.0  # Deliberately later than both frozen global deadlines.
        self.mono = 100.0
    def sleep(self, seconds):
        self.now += seconds
        self.mono += seconds


def response(status='completed', own='resp_continuation_owned', usage=True):
    return {'object': 'response', 'id': own, 'model': 'muse-wonder-1.0', 'background': True,
            'status': status, 'output': [
                {'type': 'reasoning', 'text': 'HIDDEN_DO_NOT_PERSIST'},
                {'type': 'message', 'role': 'assistant', 'status': 'completed', 'phase': 'analysis',
                 'content': [{'type': 'output_text', 'text': 'ANALYSIS_DO_NOT_PERSIST'}]},
                {'type': 'message', 'role': 'assistant', 'status': 'completed', 'phase': 'final_answer',
                 'content': [{'type': 'output_text', 'text': 'Visible math; offline-placeholder-key'}]}
            ] if status == 'completed' else [],
            'usage': {'input_tokens': 100, 'output_tokens': 200, 'total_tokens': 300}
                     if usage and status in {'completed', 'cancelled', 'incomplete'} else None}


class ContinuationGuardTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix='guard-test-', dir=Path(__file__).parent)
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        self.cont = self.root / 'continuation'
        self.ledger_path = self.root / 'ledger.json'
        self.ledger = BudgetLedger(self.ledger_path, caps={'meta': 115, 'claude': 40},
                                   initial_holds={'meta': 25, 'claude': 1})
        for name, value in (('ROOT', self.root), ('CONT_ROOT', self.cont), ('LEDGER_PATH', self.ledger_path)):
            patch = mock.patch.object(guard, name, value)
            patch.start()
            self.addCleanup(patch.stop)
        self.clock = Clock()
        self.key = mock.Mock(return_value='offline-placeholder-key')
        self.transport = mock.Mock(return_value=response())

    def run_job(self, name='math', prompt='Public math question', **kwargs):
        args = dict(transport=self.transport, key_provider=self.key,
                    wall_time=lambda: self.clock.now, monotonic=lambda: self.clock.mono,
                    sleep=self.clock.sleep)
        args.update(kwargs)
        return guard.run_meta(name, prompt, **args)

    def state(self, name='math'):
        return json.loads((self.cont / 'jobs' / name / 'state.json').read_text())

    def pending(self):
        return self.ledger.status()['providers']['meta']['pending_count']

    def test_reservation_precedes_http_old_globals_unchanged_visible_only(self):
        prior = (old.HARD_DEADLINE, old_phase.DEADLINE, old_phase.NETWORK_CUTOFF)
        def transport(method, url, payload, timeout, key):
            state = self.state()
            reservation = self.ledger.status()['reservations'][-1]
            self.assertEqual(state['phase'], 'SUBMITTING')
            self.assertEqual(reservation['reserved_usd'], '5.505024')
            self.assertEqual(reservation['status'], 'pending')
            self.assertEqual(reservation['id'], state['reservation_id'])
            self.assertEqual(payload['model'], 'muse-wonder-1.0')
            self.assertEqual(payload['reasoning'], {'effort': 'max'})
            self.assertEqual(payload['max_output_tokens'], 65536)
            self.assertLessEqual(timeout, 30)
            self.assertEqual(state['deadline_epoch']-state['started_epoch'], 900)
            return response()
        self.transport.side_effect = transport
        state = self.run_job()
        self.assertEqual(state['usage_status'], 'settled')
        self.assertEqual(state['claim_status'], 'UNVERIFIED')
        self.assertEqual(state['visible_text'], 'Visible math; [REDACTED]')
        self.assertEqual((old.HARD_DEADLINE, old_phase.DEADLINE, old_phase.NETWORK_CUTOFF), prior)
        files = ''.join(p.read_text() for p in self.cont.rglob('*.json'))
        for forbidden in ('offline-placeholder-key', 'HIDDEN_DO_NOT_PERSIST', 'ANALYSIS_DO_NOT_PERSIST'):
            self.assertNotIn(forbidden, files)
        self.assertEqual(self.ledger.status()['providers']['meta']['external_hold_usd'], '25')

    def test_global_stop_before_start_never_keys_or_reserves(self):
        self.cont.mkdir()
        (self.cont / 'STOP').write_text('stop')
        with self.assertRaises(guard.ContinuationError):
            self.run_job()
        self.key.assert_not_called()
        self.transport.assert_not_called()
        self.assertEqual(self.pending(), 0)

    def test_stop_after_creation_cancels_only_owned_id_once(self):
        self.transport.side_effect = [response('queued'), response('cancelled', usage=False)]
        def sleep(seconds):
            self.clock.sleep(seconds)
            (self.cont / 'STOP').write_text('stop')
        state = self.run_job(sleep=sleep)
        self.assertTrue(state['cancellation_confirmed'])
        self.assertEqual(self.transport.call_count, 2)
        self.assertTrue(self.transport.call_args.args[1].endswith('/resp_continuation_owned/cancel'))
        self.assertEqual(self.pending(), 1)  # Unknown cancelled usage is never refunded.

    def test_stop_race_after_key_prevents_post_and_keeps_hold(self):
        def key():
            (self.cont / 'STOP').write_text('stop')
            return 'offline-placeholder-key'
        self.key.side_effect = key
        state = self.run_job()
        self.assertEqual(state['phase'], 'SUBMISSION_UNCERTAIN')
        self.transport.assert_not_called()
        self.assertEqual(self.pending(), 1)
        self.key.reset_mock()
        self.run_job(prompt=None)
        self.key.assert_not_called()
        self.transport.assert_not_called()

    def test_unknown_submission_no_retry_or_deadline_extension(self):
        self.transport.side_effect = OSError('unsafe raw transport text')
        state = self.run_job(max_job_seconds=90)
        binding_path = self.cont / 'bindings' / 'math.json'
        original_binding = binding_path.read_bytes()
        self.assertEqual(state['phase'], 'SUBMISSION_UNCERTAIN')
        self.assertEqual(self.pending(), 1)
        self.clock.sleep(1)
        self.transport.reset_mock()
        self.key.reset_mock()
        again = self.run_job(prompt=None, max_job_seconds=1200)
        self.assertEqual(again['deadline_epoch'], state['deadline_epoch'])
        self.assertEqual(binding_path.read_bytes(), original_binding)
        self.transport.assert_not_called()
        self.key.assert_not_called()
        self.assertNotIn('unsafe raw transport text', json.dumps(again))

    def test_cancellation_interrupt_never_replays_post(self):
        def transport(method, url, payload, timeout, key):
            if url.endswith('/cancel'):
                raise KeyboardInterrupt()
            (self.cont / 'STOP').write_text('stop')
            return response('queued')
        self.transport.side_effect = transport
        with self.assertRaises(KeyboardInterrupt):
            self.run_job()
        state = self.state()
        self.assertEqual(state['phase'], 'CANCELLATION_UNCERTAIN')
        self.assertTrue(state['cancel_requested'])
        self.assertEqual(state['last_operation'], 'cancel')
        self.transport.reset_mock()
        self.key.reset_mock()
        self.assertEqual(self.run_job(prompt=None)['phase'], 'CANCELLATION_UNCERTAIN')
        self.transport.assert_not_called()
        self.key.assert_not_called()
        self.assertEqual(self.pending(), 1)

    def test_deadline_and_monotonic_budget_bound_cancel(self):
        initial_tick = self.clock.mono
        seen = []
        def transport(method, url, payload, timeout, key):
            seen.append((self.clock.mono, timeout, url))
            self.assertLessEqual(self.clock.mono + timeout, initial_tick + 60)
            return response('cancelled' if url.endswith('/cancel') else 'queued')
        self.transport.side_effect = transport
        def frozen_wall_sleep(seconds):
            self.clock.mono += seconds
        state = self.run_job(max_job_seconds=60, sleep=frozen_wall_sleep)
        self.assertTrue(state['cancellation_confirmed'])
        self.assertEqual(state['deadline_epoch'] - state['started_epoch'], 60)
        self.assertTrue(seen[-1][2].endswith('/cancel'))
        self.assertLessEqual(self.clock.mono, initial_tick + 60)

    def test_expired_owned_active_resume_makes_no_http_or_key_lookup(self):
        self.transport.side_effect = [response('queued'), KeyboardInterrupt()]
        with self.assertRaises(KeyboardInterrupt):
            self.run_job(max_job_seconds=90)
        self.clock.sleep(100)
        self.transport.reset_mock()
        self.key.reset_mock()
        state = self.run_job(prompt=None)
        self.assertEqual(state['phase'], 'CANCELLATION_UNCERTAIN')
        self.assertFalse(state['cancellation_confirmed'])
        self.transport.assert_not_called()
        self.key.assert_not_called()
        self.assertEqual(self.pending(), 1)

    def test_orphan_old_directory_and_wrong_ownership_fail_closed(self):
        self.cont.mkdir()
        (self.cont / 'jobs').mkdir()
        (self.cont / 'jobs' / 'old').mkdir()
        with self.assertRaises(guard.ContinuationError):
            self.run_job(name='old')
        self.run_job()
        path = self.cont / 'jobs' / 'math' / 'state.json'
        state = self.state()
        state['job_id'] = '0' * 32
        path.write_text(json.dumps(state))
        self.transport.reset_mock()
        self.key.reset_mock()
        with self.assertRaises(guard.ContinuationError):
            self.run_job(prompt=None)
        path.unlink()
        with self.assertRaises(guard.ContinuationError):
            self.run_job(prompt=None)
        self.transport.assert_not_called()
        self.key.assert_not_called()

    def test_binding_tamper_boolean_versions_and_changed_prompt_fail_closed(self):
        self.run_job()
        binding_path = self.cont / 'bindings' / 'math.json'
        original = binding_path.read_text()
        self.transport.reset_mock()
        self.key.reset_mock()
        with self.assertRaises(guard.ContinuationError):
            self.run_job(prompt='different prompt')
        for field, value in (('version', True), ('deadline_epoch', self.clock.now + 999999),
                             ('max_job_seconds', 1201)):
            binding = json.loads(original)
            binding[field] = value
            binding_path.write_text(json.dumps(binding))
            with self.assertRaises(guard.ContinuationError):
                self.run_job(prompt=None)
        self.transport.assert_not_called()
        self.key.assert_not_called()

    def test_caps_missing_ledger_and_budget_refusal_preserve_holds(self):
        for provider, cap in (('meta', '116'), ('claude', '41')):
            with self.ledger._locked():
                saved = self.ledger._read()
                changed = copy.deepcopy(saved)
                changed['caps_usd'][provider] = cap
                self.ledger._write(changed)
            with self.assertRaises(BudgetError):
                self.run_job(name=provider)
            with self.ledger._locked():
                self.ledger._write(saved)
        self.key.assert_not_called()
        missing = self.root / 'missing.json'
        with mock.patch.object(guard, 'LEDGER_PATH', missing):
            with self.assertRaises(BudgetError):
                self.run_job(name='missing')
        self.assertFalse(missing.exists())
        with self.ledger._locked():
            state = self.ledger._read()
            state['initial_holds_usd']['meta'] = '114'
            self.ledger._write(state)
        result = self.run_job(name='budget')
        self.assertEqual(result['phase'], 'ACCOUNTING_ERROR')
        self.transport.assert_not_called()
        self.assertEqual(self.pending(), 0)
        self.assertEqual(self.ledger.status()['providers']['meta']['external_hold_usd'], '114')

    def test_id_mismatch_not_cancelled_under_unowned_id(self):
        self.transport.side_effect = [response('queued'), response(own='resp_another_job')]
        result = self.run_job()
        self.assertEqual(result['phase'], 'PROTOCOL_UNCERTAIN')
        self.assertEqual(result['response_id'], 'resp_continuation_owned')
        self.assertEqual(self.transport.call_count, 2)
        self.assertFalse(any(call.args[1].endswith('/cancel') for call in self.transport.call_args_list))
        self.assertEqual(self.pending(), 1)

    def test_ledger_delay_past_cancel_deadline_never_enters_transport(self):
        original = guard.ExistingLedger
        def delayed_ledger(*args, **kwargs):
            path = self.cont / 'jobs' / 'math' / 'state.json'
            if path.exists() and json.loads(path.read_text()).get('cancel_requested'):
                self.clock.sleep(61)
            return original(*args, **kwargs)
        def transport(*args):
            (self.cont / 'STOP').write_text('stop')
            return response('queued')
        self.transport.side_effect = transport
        with mock.patch.object(guard, 'ExistingLedger', side_effect=delayed_ledger):
            state = self.run_job(max_job_seconds=60)
        self.assertEqual(self.transport.call_count, 1)
        self.assertEqual(state['phase'], 'CANCELLATION_UNCERTAIN')
        self.assertFalse(state['cancellation_confirmed'])
        self.assertEqual(self.pending(), 1)

    def test_request_cap_reserves_cancellation_slot(self):
        self.transport.side_effect = [response('queued'), response('cancelled')]
        result = self.run_job(max_requests=2)
        self.assertTrue(result['cancellation_confirmed'])
        self.assertEqual(result['request_count'], 2)
        self.assertEqual([c.args[0] for c in self.transport.call_args_list], ['POST', 'POST'])

    def test_malformed_limits_names_and_stale_lock(self):
        for name in ('../old', 'a/b', '', True, 'Upper'):
            with self.assertRaises(guard.ContinuationError):
                self.run_job(name=name)
        for duration in (0, 29, 1201, True, 900.0, float('nan')):
            with self.assertRaises(guard.ContinuationError):
                self.run_job(max_job_seconds=duration)
        self.cont.mkdir()
        (self.cont / 'locks').mkdir()
        (self.cont / 'locks' / 'math.lock').write_text('{"token":"stale"}')
        with self.assertRaises(FileExistsError):
            self.run_job()
        self.assertEqual((self.cont / 'locks' / 'math.lock').read_text(), '{"token":"stale"}')
        self.key.assert_not_called()
        self.transport.assert_not_called()


if __name__ == '__main__':
    unittest.main()
