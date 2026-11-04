"""Offline mocks only; no credentials or provider requests."""
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock
from budget import BudgetLedger
from hour2 import phase_guard as phase
from hour2 import claude_guard as cg
import research_client as client


class ClaudeGuardTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory(prefix='claude-guard-test-',dir=Path(__file__).parent)
        self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name)
        self.ledger_path=self.root/'ledger.json'
        self.ledger=BudgetLedger(self.ledger_path,caps={'meta':115,'claude':40})
        for name,value in (('PHASE_ROOT',self.root),('LEDGER_PATH',self.ledger_path)):
            patch=mock.patch.object(phase,name,value);patch.start();self.addCleanup(patch.stop)
        self.now=phase.START+10
        self.clock=lambda:self.now
        phase.initialize_phase(wall_time=self.clock)
    def run_job(self,job='test',prompt='Public mathematics',**kwargs):
        return cg.run_claude(job,prompt,wall_time=self.clock,monotonic=lambda:100,**kwargs)
    def test_timeout_never_resubmits_and_retains_fake_worker_hold(self):
        def worker(payload,timeout):
            phase.PhaseLedger(wall_time=self.clock).reserve('claude','3.4',purpose='offline test')
            return {'kind':'timeout','stdout':b'secret not saved'}
        runner=mock.Mock(side_effect=worker)
        first=self.run_job(process_runner=runner,max_job_seconds=1200)
        self.assertEqual(first['status'],'UNCERTAIN')
        self.assertEqual(self.ledger.status()['providers']['claude']['pending_count'],1)
        second=self.run_job(prompt=None,process_runner=runner)
        self.assertEqual(second['status'],'UNCERTAIN');self.assertEqual(runner.call_count,1)
        self.assertNotIn('secret',(self.root/'claude-jobs/test/state.json').read_text())
    def test_expiry_old_jobs_and_invalid_names_reject_before_worker(self):
        runner=mock.Mock()
        self.now=phase.NETWORK_CUTOFF
        with self.assertRaises(phase.PhaseError):self.run_job(process_runner=runner)
        self.now=phase.START+10
        for name in ('../old','/outside','OLD'):
            with self.assertRaises(phase.PhaseError):self.run_job(job=name,process_runner=runner)
        output=self.root/'claude-jobs/old';output.mkdir(parents=True)
        (output/'state.json').write_text(json.dumps({'version':1,'phase_id':'old'}))
        with self.assertRaises(phase.PhaseError):self.run_job(job='old',process_runner=runner)
        runner.assert_not_called()
    def test_worker_deadline_and_token_caps_are_bounded(self):
        runner=mock.Mock(return_value={'kind':'timeout','stdout':b''})
        self.now=phase.NETWORK_CUTOFF-20
        self.run_job(process_runner=runner,max_job_seconds=1800)
        payload,timeout=runner.call_args.args
        self.assertEqual(payload['deadline_epoch'],phase.NETWORK_CUTOFF)
        self.assertLessEqual(timeout,20)
        self.assertEqual(payload['max_tokens'],65536)
        for kwargs in ({'max_job_seconds':1801},{'max_job_seconds':True},{'max_tokens':65537}):
            with self.assertRaises(phase.PhaseError):self.run_job(job='other',process_runner=runner,**kwargs)
    def test_crashed_starting_state_never_relaunches(self):
        runner=mock.Mock(side_effect=KeyboardInterrupt())
        with self.assertRaises(KeyboardInterrupt):self.run_job(process_runner=runner)
        result=self.run_job(prompt=None,process_runner=runner)
        self.assertEqual(result['status'],'UNCERTAIN')
        self.assertEqual(result['error_category'],'prior_worker_outcome_unknown')
        self.assertEqual(runner.call_count,1)
    def test_worker_reserves_before_http_and_settles_visible_usage(self):
        payload={'phase_id':phase.PHASE_ID,'prompt':'Public only','started_epoch':self.now,
                 'deadline_epoch':self.now+1200,'max_tokens':65536}
        response={'type':'message','model':client.MODEL,'content':[{'type':'thinking','thinking':'hidden'},
                    {'type':'text','text':'visible offline-key'}],'stop_reason':'end_turn',
                    'usage':{'input_tokens':10,'output_tokens':20}}
        def opened(request,timeout):
            rows=self.ledger.status()['reservations']
            self.assertEqual(len(rows),1);self.assertEqual(rows[0]['status'],'pending')
            self.assertEqual(request.full_url,client.API_URL)
            body=json.loads(request.data)
            self.assertEqual(body['output_config'],{'effort':'max'})
            self.assertEqual(body['max_tokens'],65536)
            self.assertLessEqual(timeout,1200)
            return io.BytesIO(json.dumps(response).encode())
        with mock.patch.object(client,'_read_api_key',return_value='offline-key') as key, mock.patch.object(client,'_open_request',side_effect=opened) as transport:
            result=cg._worker(payload,wall=self.clock,mono=lambda:100)
        self.assertTrue(result['ok'],result)
        self.assertEqual(result['text'],'visible [REDACTED]')
        self.assertNotIn('hidden',json.dumps(result))
        self.assertEqual(result['usage_status'],'settled')
        self.assertEqual(self.ledger.status()['providers']['claude']['pending_count'],0)
        key.assert_called_once();transport.assert_called_once()
    def test_worker_rejects_expired_before_key_or_http(self):
        self.now=phase.NETWORK_CUTOFF
        with mock.patch.object(client,'_read_api_key') as key,mock.patch.object(client,'_open_request') as transport:
            result=cg._worker({},wall=self.clock,mono=lambda:100)
        self.assertFalse(result['ok']);key.assert_not_called();transport.assert_not_called()
    def test_cap_guard_refuses_before_worker(self):
        with self.ledger._locked():
            state=self.ledger._read();state['caps_usd']['claude']='41';self.ledger._write(state)
        runner=mock.Mock()
        with self.assertRaises(Exception):self.run_job(process_runner=runner)
        runner.assert_not_called()
    def test_malformed_output_is_not_persisted(self):
        result=self.run_job(process_runner=lambda payload,timeout:{'kind':'completed','stdout':b'{raw secret'})
        self.assertEqual(result['status'],'UNCERTAIN')
        self.assertNotIn('secret',(self.root/'claude-jobs/test/state.json').read_text())
    def test_capture_fixed_shell_false_process_and_timeout(self):
        fake=mock.Mock();fake.stdin=io.BytesIO();fake.stdout=io.BytesIO(b'{}');fake.stderr=io.BytesIO()
        fake.poll.side_effect=[None,0,0];fake.returncode=-9
        with mock.patch.object(cg.subprocess,'Popen',return_value=fake) as popen, \
             mock.patch.object(cg.time,'monotonic',side_effect=[0,1,2,3,4]),mock.patch.object(cg.time,'sleep'):
            result=cg._capture({'prompt':'public'},.1)
        self.assertEqual(result['kind'],'timeout');fake.kill.assert_called_once()
        self.assertFalse(popen.call_args.kwargs['shell'])
        self.assertEqual(popen.call_args.args[0][-3:],['-m','hour2.claude_guard','--worker'])


if __name__=='__main__':unittest.main()
