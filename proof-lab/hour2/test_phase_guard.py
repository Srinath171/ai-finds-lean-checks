"""Offline hour-two isolation/cap/deadline tests; never real keys or requests."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock
from budget import BudgetLedger,BudgetError
from frontier import background_meta as old
from hour2 import phase_guard as guard


class Clock:
    def __init__(self,now=None):self.now=guard.START+60 if now is None else now;self.mono=100.0
    def sleep(self,seconds):self.now+=seconds;self.mono+=seconds


def response(status='completed'):
    return {'object':'response','id':'resp_hour2_owned','model':'muse-wonder-1.0','background':True,
            'status':status,'output':[{'type':'message','role':'assistant','status':'completed',
            'content':[{'type':'output_text','text':'Public math result'}]}] if status=='completed' else [],
            'usage':{'input_tokens':100,'output_tokens':200,'total_tokens':300} if status=='completed' else None}


class PhaseGuardTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory(prefix='phase-test-',dir=Path(__file__).parent)
        self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name)
        self.phase=self.root/'phase'
        self.ledger_path=self.root/'ledger.json'
        self.ledger=BudgetLedger(self.ledger_path,caps={'meta':115,'claude':40},initial_holds={'meta':25,'claude':1})
        for name,value in (('PHASE_ROOT',self.phase),('LEDGER_PATH',self.ledger_path)):
            patch=mock.patch.object(guard,name,value);patch.start();self.addCleanup(patch.stop)
        self.clock=Clock()
        self.key=mock.Mock(return_value='offline-placeholder-key')
        self.transport=mock.Mock(return_value=response())
        guard.initialize_phase(wall_time=lambda:self.clock.now)
    def run_job(self,name='math',prompt='Public mathematics only',**kwargs):
        arguments=dict(max_job_seconds=1200,transport=self.transport,key_provider=self.key,
                       wall_time=lambda:self.clock.now,monotonic=lambda:self.clock.mono,sleep=self.clock.sleep)
        arguments.update(kwargs)
        return guard.run_meta(name,prompt,**arguments)
    def state(self,name='math'):
        return json.loads((self.phase/'jobs'/name/'state.json').read_text())

    def test_reservation_precedes_transport_and_old_module_unchanged(self):
        old_deadline=old.HARD_DEADLINE
        old_globals=old.run_background.__globals__['HARD_DEADLINE']
        def transport(method,url,payload,timeout,key):
            state=self.state()
            rows=self.ledger.status()['reservations']
            self.assertEqual(state['phase'],'SUBMITTING')
            self.assertEqual(rows[-1]['reserved_usd'],'5.505024')
            self.assertEqual(rows[-1]['status'],'pending')
            self.assertEqual(rows[-1]['id'],state['reservation_id'])
            self.assertEqual(payload['model'],'muse-wonder-1.0')
            self.assertEqual(payload['reasoning'],{'effort':'max'})
            self.assertLessEqual(timeout,30)
            self.assertGreaterEqual(state['started_epoch'],guard.START)
            self.assertLessEqual(state['deadline_epoch'],guard.NETWORK_CUTOFF)
            return response()
        self.transport.side_effect=transport
        result=self.run_job()
        self.assertEqual(result['usage_status'],'settled')
        self.assertEqual(old.HARD_DEADLINE,old_deadline)
        self.assertEqual(old.run_background.__globals__['HARD_DEADLINE'],old_globals)
        self.assertLess(old_deadline,guard.START)

    def test_config_created_once_no_reset_and_tamper_rejected(self):
        path=self.phase/'phase_budget.json'
        original=path.read_bytes()
        guard.initialize_phase(wall_time=lambda:self.clock.now)
        self.assertEqual(path.read_bytes(),original)
        changed=json.loads(original);changed['deadline_utc']='2026-11-05T20:48:30+00:00'
        path.write_text(json.dumps(changed))
        with self.assertRaises(guard.PhaseError):guard.initialize_phase(wall_time=lambda:self.clock.now)
        with self.assertRaises(guard.PhaseError):self.run_job()
        self.assertEqual(json.loads(path.read_text()),changed)
        self.key.assert_not_called();self.transport.assert_not_called()

    def test_expired_or_not_started_phase_never_keys_or_transport(self):
        for now in (guard.START-1,guard.NETWORK_CUTOFF,guard.DEADLINE+1):
            self.clock.now=now
            with self.assertRaises(guard.PhaseError):self.run_job()
        self.key.assert_not_called();self.transport.assert_not_called()
        self.assertEqual(self.ledger.status()['providers']['meta']['pending_count'],0)

    def test_job_limit_and_new_directory_only(self):
        for name in ('../frontier/background-meta','a/b','',True,'X'):
            with self.assertRaises(guard.PhaseError):self.run_job(name=name)
        for duration in (1801,True,0,float('nan')):
            with self.assertRaises(guard.PhaseError):self.run_job(max_job_seconds=duration)
        output=self.phase/'jobs'/'old-job';output.mkdir(parents=True)
        (output/'state.json').write_text(json.dumps({'response_id':'resp_old','started_epoch':old.HARD_DEADLINE-100}))
        before=(output/'state.json').read_bytes()
        with self.assertRaises(guard.PhaseError):self.run_job(name='old-job')
        self.assertEqual((output/'state.json').read_bytes(),before)
        self.key.assert_not_called();self.transport.assert_not_called()

    def test_uncertain_post_never_auto_resubmitted_or_refunded(self):
        self.transport.side_effect=OSError('offline transport failure')
        result=self.run_job()
        self.assertEqual(result['phase'],'SUBMISSION_UNCERTAIN')
        self.assertEqual(self.ledger.status()['providers']['meta']['pending_count'],1)
        self.transport.reset_mock();self.key.reset_mock()
        resumed=self.run_job(prompt=None)
        self.assertEqual(resumed['phase'],'SUBMISSION_UNCERTAIN')
        self.transport.assert_not_called();self.key.assert_not_called()
        self.assertEqual(self.ledger.status()['providers']['meta']['pending_count'],1)

    def test_resume_cannot_extend_deadline_or_adopt_prephase_state(self):
        first=self.run_job(max_job_seconds=100)
        deadline=first['deadline_epoch']
        self.clock.sleep(1)
        self.transport.reset_mock();self.key.reset_mock()
        resumed=self.run_job(prompt=None,max_job_seconds=1800)
        self.assertEqual(resumed['deadline_epoch'],deadline)
        self.transport.assert_not_called();self.key.assert_not_called()
        path=self.phase/'jobs'/'math'/'state.json'
        state=json.loads(path.read_text());state['started_epoch']=guard.START-10
        path.write_text(json.dumps(state))
        with self.assertRaises(guard.PhaseError):self.run_job(prompt=None)
        self.transport.assert_not_called();self.key.assert_not_called()

    def test_both_caps_checked_on_every_ledger_read(self):
        for provider,cap in (('meta','116'),('claude','41')):
            with self.ledger._locked():
                state=self.ledger._read();saved=copy.deepcopy(state)
                state['caps_usd'][provider]=cap;self.ledger._write(state)
            with self.assertRaises(BudgetError):guard.PhaseLedger(wall_time=lambda:self.clock.now)
            with self.ledger._locked():self.ledger._write(saved)
        status=guard.PhaseLedger(wall_time=lambda:self.clock.now).status()['providers']
        self.assertEqual(status['meta']['cap_usd'],'115')
        self.assertEqual(status['claude']['cap_usd'],'40')

    def test_budget_refusal_never_posts_and_keeps_existing_holds(self):
        with self.ledger._locked():
            state=self.ledger._read();state['initial_holds_usd']['meta']='114';self.ledger._write(state)
        result=self.run_job()
        self.assertEqual(result['phase'],'ACCOUNTING_ERROR')
        self.transport.assert_not_called()
        status=self.ledger.status()['providers']['meta']
        self.assertEqual(status['external_hold_usd'],'114')
        self.assertEqual(status['pending_count'],0)

    def test_cutoff_cancellation_finishes_before_phase_end_minus_fifteen(self):
        self.clock.now=guard.NETWORK_CUTOFF-40
        times=[]
        def transport(method,url,payload,timeout,key):
            times.append((self.clock.now,timeout,url))
            self.assertLessEqual(self.clock.now+timeout,guard.NETWORK_CUTOFF)
            return response('cancelled' if url.endswith('/cancel') else 'queued')
        self.transport.side_effect=transport
        result=self.run_job()
        self.assertTrue(result['cancellation_confirmed'])
        self.assertEqual(result['deadline_epoch'],guard.NETWORK_CUTOFF)
        self.assertTrue(all(now<guard.NETWORK_CUTOFF for now,_,_ in times))
        self.assertTrue(times[-1][2].endswith('/cancel'))

    def test_orphan_initialization_fails_closed_and_no_key_is_saved(self):
        self.run_job()
        saved=''.join(path.read_text() for path in self.phase.rglob('*.json'))
        self.assertNotIn('offline-placeholder-key',saved)
        path=self.phase/'bindings'/'orphan.json'
        path.write_text(json.dumps({'phase_id':guard.PHASE_ID,'job_name':'orphan','output_relative':'jobs/orphan',
                                   'created_epoch':self.clock.now,'job_id':None}))
        self.transport.reset_mock();self.key.reset_mock()
        with self.assertRaises(guard.PhaseError):self.run_job(name='orphan')
        self.transport.assert_not_called();self.key.assert_not_called()


if __name__=='__main__':unittest.main()
