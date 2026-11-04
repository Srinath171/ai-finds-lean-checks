"""Offline transport/state/accounting tests; no actual key or service access."""
import copy
import io
import json
from pathlib import Path
import tempfile
import threading
import time
import unittest
import urllib.error
from unittest import mock

from budget import BudgetLedger
from frontier import background_meta as bg


class Clock:
    def __init__(self, now=None):
        self.now = bg.HARD_DEADLINE - 10000 if now is None else now
        self.mono = 100.0
    def sleep(self, seconds):
        self.now += seconds
        self.mono += seconds


def response(status='queued', *, response_id='resp_owned123', text=None, usage=None):
    data = {'object':'response','id':response_id,'model':bg.MODEL,'background':True,
            'status':status,'output':[]}
    if text is not None:
        data['output']=[{'type':'message','role':'assistant','status':'completed',
                         'content':[{'type':'output_text','text':text}]}]
    if usage is not None:
        data['usage']=usage
    return data


USAGE={'input_tokens':100,'output_tokens':200,'total_tokens':300,
       'output_tokens_details':{'reasoning_tokens':150}}


class BackgroundTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory(prefix='background-test-',dir=Path(__file__).parent)
        self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name)
        self.output=self.root/'job'
        self.ledger_path=self.root/'spending.json'
        self.ledger=BudgetLedger(self.ledger_path,initial_holds={'meta':25,'claude':1})
        patch=mock.patch.object(bg,'LEDGER_PATH',self.ledger_path)
        patch.start()
        self.addCleanup(patch.stop)
        self.clock=Clock()
        self.key=mock.Mock(return_value='offline-secret-sentinel')
        self.transport=mock.Mock(side_effect=[response(),response('completed',text='Public mathematical result',usage=USAGE)])
    def run_job(self,prompt='Public mathematics only',**kwargs):
        options=dict(output_dir=self.output,transport=self.transport,key_provider=self.key,
                     wall_time=lambda:self.clock.now,monotonic=lambda:self.clock.mono,sleep=self.clock.sleep)
        options.update(kwargs)
        return bg.run_background(prompt,**options)
    def pending(self):
        return self.ledger.status()['providers']['meta']['pending_count']
    def test_reserve_and_durable_submission_before_transport(self):
        def transport(method,url,payload,timeout,key):
            state=json.loads((self.output/'state.json').read_text())
            self.assertEqual(state['phase'],'SUBMITTING')
            self.assertEqual(state['request_count'],1)
            row=self.ledger.status()['reservations'][0]
            self.assertEqual(row['reserved_usd'],'5.505024')
            self.assertEqual(state['reservation_id'],row['id'])
            self.assertEqual(payload,{'model':bg.MODEL,'input':'Public mathematics only','reasoning':{'effort':'max'},'max_output_tokens':65536,'background':True})
            self.assertEqual(url,bg.BASE)
            self.assertLessEqual(timeout,30)
            return response('completed',text='Result',usage=USAGE)
        self.transport.side_effect=transport
        state=self.run_job()
        self.assertEqual(state['usage_status'],'settled')
        self.assertEqual(state['cost_usd'],'0.0044')
        self.assertTrue(state['finished'])
        self.assertEqual(state['claim_status'],'UNVERIFIED')
        self.assertEqual(self.pending(),0)
    def test_queued_in_progress_and_all_terminal_statuses(self):
        for status in ('completed','incomplete','failed','cancelled'):
            with self.subTest(status=status):
                output=self.root/status
                transport=mock.Mock(side_effect=[response(),response('in_progress'),response(status,text='Visible',usage=USAGE)])
                result=self.run_job(output_dir=output,transport=transport)
                self.assertEqual(result['remote_status'],status)
                self.assertEqual(result['phase'],'TERMINAL')
                self.assertTrue(result['finished'])
                self.assertEqual(result['incomplete'],status!='completed')
                self.assertEqual(result['usage_status'],'settled')
                self.assertEqual(transport.call_count,3)
    def test_hidden_reasoning_commentary_headers_and_raw_fields_never_saved(self):
        raw=response('completed',text='Only visible final mathematics',usage=USAGE)
        raw['output'].insert(0,{'type':'reasoning','encrypted_content':'hidden-secret','summary':['hidden-secret']})
        raw['output'].append({'type':'message','role':'assistant','phase':'commentary','status':'completed',
                              'content':[{'type':'output_text','text':'commentary-secret'}]})
        raw['headers']={'Authorization':'offline-secret-sentinel'}
        raw['arbitrary']='raw-secret'
        self.transport.side_effect=[raw]
        state=self.run_job()
        saved=''.join(p.read_text() for p in self.output.iterdir() if p.is_file())
        for forbidden in ('hidden-secret','commentary-secret','offline-secret-sentinel','raw-secret','Authorization'):
            self.assertNotIn(forbidden,saved)
        self.assertEqual(state['visible_text'],'Only visible final mathematics')
    def test_explicit_final_phase_excludes_commentary_analysis_and_redacts_key(self):
        raw=response('completed',text='unphased final',usage=USAGE)
        for phase,text in (('final_answer','explicit final offline-secret-sentinel'),('commentary','commentary-only'),('analysis','analysis-only')):
            raw['output'].append({'type':'message','role':'assistant','status':'completed','phase':phase,
                                  'content':[{'type':'output_text','text':text}]})
        self.transport.side_effect=[raw]
        state=self.run_job()
        self.assertEqual(state['visible_text'],'unphased final\nexplicit final [REDACTED]')
        saved=(self.output/'state.json').read_text()
        for hidden in ('offline-secret-sentinel','commentary-only','analysis-only'):
            self.assertNotIn(hidden,saved)
    def test_settlement_resume_crash_window_and_inconsistent_state_rejected(self):
        self.transport.side_effect=[response('completed',text='visible',usage=USAGE)]
        self.run_job()
        path=self.output/'state.json'
        state=json.loads(path.read_text())
        state.update(usage_status='pending',cost_usd=None)
        path.write_text(json.dumps(state))
        self.transport.reset_mock()
        recovered=self.run_job(prompt=None)
        self.assertEqual(recovered['usage_status'],'settled')
        self.transport.assert_not_called()
        corrupted=copy.deepcopy(recovered)
        corrupted.update(phase='ACTIVE',remote_status='in_progress',finished=False,usage=None,
                         usage_status='pending',cost_usd=None,visible_text='')
        path.write_text(json.dumps(corrupted))
        with self.assertRaises(bg.SafeError):self.run_job(prompt=None)
        corrupted=copy.deepcopy(recovered)
        corrupted['cost_usd']='0.1'
        path.write_text(json.dumps(corrupted))
        with self.assertRaises(bg.SafeError):self.run_job(prompt=None)
        self.transport.assert_not_called()
    def test_missing_invalid_or_inconsistent_usage_keeps_hold_even_empty(self):
        invalid=[None, {'input_tokens':True,'output_tokens':2}, {'input_tokens':-1,'output_tokens':2},
                 {'input_tokens':1,'output_tokens':2,'total_tokens':4},
                 {'input_tokens':1,'output_tokens':2,'output_tokens_details':{'reasoning_tokens':3}}]
        for index,usage in enumerate(invalid):
            state=self.run_job(output_dir=self.root/str(index),transport=mock.Mock(return_value=response('completed',text='',usage=usage)))
            self.assertTrue(state['finished'])
            self.assertTrue(state['incomplete'])
            self.assertEqual(state['usage_status'],'pending')
        self.assertEqual(self.pending(),len(invalid))
    def test_incomplete_empty_response_still_settles_valid_usage(self):
        self.transport.side_effect=[response('incomplete',text='',usage=USAGE)]
        state=self.run_job()
        self.assertTrue(state['incomplete'])
        self.assertEqual(state['usage_status'],'settled')
    def test_unknown_post_never_auto_resubmits_or_releases_hold(self):
        self.transport.side_effect=bg.SafeError('transport_timeout')
        first=self.run_job()
        self.assertEqual(first['phase'],'SUBMISSION_UNCERTAIN')
        self.assertFalse(first['finished'])
        self.assertEqual(self.pending(),1)
        self.transport.reset_mock()
        self.key.reset_mock()
        second=self.run_job(prompt=None)
        self.assertEqual(second['reservation_id'],first['reservation_id'])
        self.transport.assert_not_called()
        self.key.assert_not_called()
    def test_resume_only_saved_owned_id_without_another_post(self):
        self.transport.side_effect=[response(),KeyboardInterrupt()]
        with self.assertRaises(KeyboardInterrupt): self.run_job()
        old=json.loads((self.output/'state.json').read_text())
        resumed_transport=mock.Mock(return_value=response('completed',text='Result',usage=USAGE))
        result=self.run_job(prompt=None,transport=resumed_transport,max_job_seconds=3600)
        method,url,_,_,_=resumed_transport.call_args.args
        self.assertEqual((method,url),('GET',bg.BASE+'/resp_owned123'))
        self.assertEqual(result['reservation_id'],old['reservation_id'])
        self.assertEqual(result['deadline_epoch'],old['deadline_epoch'])
        self.assertEqual(len(self.ledger.status()['reservations']),1)
    def test_returned_id_mismatch_never_fetched_cancelled_or_settled(self):
        self.transport.side_effect=[response(),response('completed',response_id='resp_other',text='Wrong',usage=USAGE)]
        result=self.run_job()
        self.assertEqual(result['phase'],'PROTOCOL_UNCERTAIN')
        self.assertEqual(result['response_id'],'resp_owned123')
        self.assertFalse(result['finished'])
        self.assertEqual(self.pending(),1)
        self.assertEqual(self.transport.call_count,2)
        self.assertTrue(all('resp_other' not in call.args[1] for call in self.transport.call_args_list))
    def test_malformed_creation_output_preserves_owned_id_for_cancellation(self):
        bad=response('completed',usage=USAGE)
        bad['output']='malformed'
        self.transport.side_effect=[bad,response('cancelled')]
        state=self.run_job()
        self.assertEqual(state['response_id'],'resp_owned123')
        self.assertEqual(self.transport.call_args.args[1],bg.BASE+'/resp_owned123/cancel')
        self.assertTrue(state['cancellation_confirmed'])
        self.assertEqual(self.pending(),1)
    def test_stop_file_cancel_success_race_completion_and_failure(self):
        for index,outcome in enumerate((response('cancelled'),response('completed',text='Won race',usage=USAGE),bg.SafeError('http_error',503))):
            output=self.root/('cancel'+str(index))
            def transport(method,url,payload,timeout,key):
                if url==bg.BASE:
                    (output/'STOP').touch()
                    return response()
                self.assertEqual(url,bg.BASE+'/resp_owned123/cancel')
                if isinstance(outcome,Exception): raise outcome
                return outcome
            state=self.run_job(output_dir=output,transport=transport)
            if isinstance(outcome,Exception):
                self.assertEqual(state['phase'],'CANCELLATION_UNCERTAIN')
                self.assertFalse(state['finished'])
                self.assertEqual(state['usage_status'],'pending')
            else:
                self.assertTrue(state['finished'])
                self.assertEqual(state['cancellation_confirmed'],index==0)
                if index==1:self.assertEqual(state['usage_status'],'settled')
    def test_interrupted_cancellation_and_legacy_intent_never_replay_post(self):
        def transport(method,url,payload,timeout,key):
            if url == bg.BASE:
                (self.output/'STOP').touch()
                return response()
            self.assertEqual(url,bg.BASE+'/resp_owned123/cancel')
            durable=json.loads((self.output/'state.json').read_text())
            self.assertEqual(durable['phase'],'CANCELLATION_UNCERTAIN')
            self.assertTrue(durable['cancel_requested'])
            self.assertEqual(durable['last_operation'],'cancel')
            raise KeyboardInterrupt()
        with self.assertRaises(KeyboardInterrupt): self.run_job(transport=transport)
        saved=json.loads((self.output/'state.json').read_text())
        self.assertEqual(saved['request_count'],2)
        self.assertEqual(self.pending(),1)
        for phase,operation in (('CANCELLATION_UNCERTAIN','cancel'),('ACTIVE','cancel'),('ACTIVE','start'),('ACCEPTED_UNKNOWN','cancel')):
            state=copy.deepcopy(saved)
            state.update(phase=phase,last_operation=operation)
            (self.output/'state.json').write_text(json.dumps(state))
            self.transport.reset_mock()
            self.key.reset_mock()
            resumed=self.run_job(prompt=None)
            self.assertEqual(resumed['phase'],'CANCELLATION_UNCERTAIN')
            self.assertEqual(resumed['request_count'],2)
            self.assertFalse(resumed['finished'])
            self.assertEqual(resumed['usage_status'],'pending')
            self.assertEqual(self.pending(),1)
            self.transport.assert_not_called()
            self.key.assert_not_called()
    def test_strict_saved_metadata_refuses_before_any_transport(self):
        self.transport.side_effect=[response(),KeyboardInterrupt()]
        with self.assertRaises(KeyboardInterrupt):self.run_job()
        saved=json.loads((self.output/'state.json').read_text())
        cases=[{'version':True},{'cancellation_confirmed':True},
               {'last_operation':{'raw':'must-not-persist'}},{'last_operation':'other'},
               {'last_operation':'cancel','cancel_requested':False},
               {'cancel_reason':{'raw':'must-not-persist'}},{'cancel_reason':'other'},
               {'error_category':{'raw':'must-not-persist'}},{'error_category':'other'},
               {'cancel_requested':True,'cancellation_confirmed':True,'cancel_reason':'stop_file'}]
        for changed in cases:
            state=copy.deepcopy(saved)
            state.update(changed)
            (self.output/'state.json').write_text(json.dumps(state))
            self.transport.reset_mock()
            self.key.reset_mock()
            with self.subTest(changed=changed),self.assertRaises(bg.SafeError):self.run_job(prompt=None)
            self.transport.assert_not_called()
            self.key.assert_not_called()
    def test_deadline_and_request_cap_leave_cancellation_capacity(self):
        self.clock=Clock(bg.HARD_DEADLINE-25)
        calls=[]
        def transport(method,url,payload,timeout,key):
            calls.append((url,self.clock.now,timeout))
            return response('cancelled') if url.endswith('/cancel') else response()
        result=self.run_job(transport=transport)
        self.assertTrue(result['cancellation_confirmed'])
        self.assertLessEqual(calls[-1][1],bg.HARD_DEADLINE-10)
        self.assertLessEqual(calls[-1][1]+calls[-1][2],bg.HARD_DEADLINE)
        self.clock=Clock()
        transport=mock.Mock(side_effect=[response(),response('in_progress'),response('cancelled')])
        result=self.run_job(output_dir=self.root/'requestcap',transport=transport,max_requests=3)
        self.assertEqual(result['request_count'],3)
        self.assertTrue(transport.call_args.args[1].endswith('/cancel'))
    def test_stop_before_transport_and_expired_deadline_make_no_request(self):
        def key():
            (self.output/'STOP').touch()
            return 'offline-secret-sentinel'
        state=self.run_job(key_provider=key)
        self.assertEqual(state['phase'],'SUBMISSION_UNCERTAIN')
        self.transport.assert_not_called()
        self.clock=Clock(bg.HARD_DEADLINE-5)
        with self.assertRaises(bg.SafeError): self.run_job(output_dir=self.root/'expired')
        self.transport.assert_not_called()
    def test_missing_oversized_cap_and_insufficient_ledger_refuse(self):
        with mock.patch.object(bg,'LEDGER_PATH',self.root/'missing.json'), self.assertRaises(bg.SafeError):
            self.run_job()
        self.assertFalse((self.root/'missing.json').exists())
        oversized=self.root/'oversized.json'
        BudgetLedger(oversized,caps={'meta':126,'claude':40})
        with mock.patch.object(bg,'LEDGER_PATH',oversized),self.assertRaises(bg.SafeError):self.run_job()
        small=self.root/'small.json'
        BudgetLedger(small,initial_holds={'meta':124,'claude':0})
        with mock.patch.object(bg,'LEDGER_PATH',small):
            self.assertEqual(self.run_job()['phase'],'ACCOUNTING_ERROR')
        self.transport.assert_not_called()
    def test_owned_receipt_tampering_and_unknown_state_fields_refuse(self):
        self.transport.side_effect=[response(),KeyboardInterrupt()]
        with self.assertRaises(KeyboardInterrupt):self.run_job()
        receipt=json.loads((self.output/'accepted.json').read_text())
        receipt['response_id']='resp_other'
        (self.output/'accepted.json').write_text(json.dumps(receipt))
        self.transport.reset_mock()
        with self.assertRaises(bg.SafeError): self.run_job(prompt=None)
        self.transport.assert_not_called()
        receipt['response_id']='resp_owned123'
        (self.output/'accepted.json').write_text(json.dumps(receipt))
        state=json.loads((self.output/'state.json').read_text())
        state['raw_response']='must-not-print'
        (self.output/'state.json').write_text(json.dumps(state))
        with self.assertRaises(bg.SafeError): self.run_job(prompt=None)
    def test_lock_ids_and_limits_are_fail_closed(self):
        self.output.mkdir()
        (self.output/'session.lock').touch()
        with self.assertRaises(FileExistsError):self.run_job()
        self.transport.assert_not_called()
        for bad in ('https://evil/resp_x','resp_x/../../other','resp_x?query=1','resp_','rs_reasoning',True):
            with self.assertRaises(bg.SafeError): bg._url('poll',bad)
        for kwargs in ({'max_requests':251},{'max_requests':True},{'max_job_seconds':3601},{'poll_interval':16}):
            with self.assertRaises(bg.SafeError):self.run_job(output_dir=self.root/'limits',**kwargs)
    def test_http_transport_rejects_redirect_and_bounds_wait(self):
        redirect=urllib.error.HTTPError(bg.BASE,302,'raw-secret',{'Location':'https://evil'},io.BytesIO(b'raw-secret'))
        opener=mock.Mock()
        opener.open.side_effect=redirect
        with mock.patch.object(bg.urllib.request,'build_opener',return_value=opener):
            with self.assertRaises(bg.SafeError) as raised:
                bg.http_transport('POST',bg.BASE,{},1,'offline-secret-sentinel')
        self.assertEqual(raised.exception.category,'redirect_rejected')
        self.assertNotIn('raw-secret',str(raised.exception))
        self.assertIsNone(bg._NoRedirect().redirect_request(None,None,302,'',{},'https://evil'))
        release=threading.Event()
        opener.open.side_effect=lambda *a,**k: release.wait(.2)
        start=time.monotonic()
        try:
            with mock.patch.object(bg.urllib.request,'build_opener',return_value=opener),self.assertRaises(bg.SafeError) as raised:
                bg.http_transport('POST',bg.BASE,{},.01,'offline-secret-sentinel')
            self.assertEqual(raised.exception.category,'transport_timeout')
            self.assertLess(time.monotonic()-start,.15)
        finally:release.set()
        with self.assertRaises(bg.SafeError):
            bg.http_transport('GET','https://evil/resp_x',None,1,'offline-secret-sentinel')
    def test_invalid_response_shapes_and_stored_reasoning_usage_rejected(self):
        for changed in ({'id':'bad'},{'status':'nonsense'},{'model':'other'},{'output':{}},{'object':'other'}):
            data=response('completed',text='visible')
            data.update(changed)
            with self.assertRaises(bg.SafeError):bg.sanitize_response(data,own_id='resp_owned123')
        self.transport.side_effect=[response('completed',text='visible',usage=USAGE)]
        self.run_job()
        path=self.output/'state.json'
        state=json.loads(path.read_text())
        state['usage']['reasoning_tokens']='hidden-secret'
        path.write_text(json.dumps(state))
        with self.assertRaises(bg.SafeError):self.run_job(prompt=None)


if __name__=='__main__':
    unittest.main()
