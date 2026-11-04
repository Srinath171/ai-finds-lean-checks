"""Ledger integration through mocked urllib only; no keys or network."""
import io
import json
import sys
import tempfile
import unittest
import urllib.error
from decimal import Decimal
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import prover
from budget import BudgetLedger


class ApiBudgetTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(prefix='api-budget-test-', dir=Path(__file__).parent)
        self.path=Path(self.tmp.name)/'spending.json'
        self.patch=mock.patch.object(prover,'SPENDING_LEDGER_PATH',self.path)
        self.patch.start()

    def tearDown(self):
        self.patch.stop()
        self.tmp.cleanup()

    def call(self, **kwargs):
        return prover.chat_completion(model='muse-wonder-1.0',
            messages=[{'role':'user','content':'Give a proof.'}],
            api_key='offline-test-placeholder',max_tokens=kwargs.pop('max_tokens',100),**kwargs)

    @staticmethod
    def response(usage=None, content='rfl', finish_reason='stop'):
        data={'choices':[{'message':{'content':content}, 'finish_reason':finish_reason}]}
        if usage is not None: data['usage']=usage
        return io.BytesIO(json.dumps(data).encode())

    def test_reserve_precedes_transport_and_exact_usage_settles(self):
        def transport(request,**kwargs):
            status=BudgetLedger(self.path).status()
            self.assertEqual(status['providers']['meta']['pending_count'],1)
            reservation=status['reservations'][0]
            bound=(Decimal(len(request.data)+4096)*4+Decimal(100)*20)/1_000_000
            self.assertEqual(Decimal(reservation['reserved_usd']),bound)
            self.assertEqual(status['providers']['meta']['external_hold_usd'],'25')
            return self.response({'prompt_tokens':10,'completion_tokens':20})
        with mock.patch.object(prover.urllib.request,'urlopen',side_effect=transport):
            result=self.call()
        self.assertEqual(result.content,'rfl')
        status=BudgetLedger(self.path).status()
        self.assertEqual(status['providers']['meta']['pending_count'],0)
        self.assertEqual(status['providers']['meta']['settled_count'],1)
        self.assertEqual(Decimal(status['reservations'][0]['actual_usd']),Decimal('0.00044'))

    def test_cap_denies_before_transport(self):
        BudgetLedger(self.path,initial_holds={'meta':125,'claude':0})
        with mock.patch.object(prover.urllib.request,'urlopen') as transport:
            with self.assertRaisesRegex(prover.ApiError,'ledger refused'):
                self.call()
            transport.assert_not_called()

    def test_existing_holds_and_caps_are_preserved(self):
        BudgetLedger(self.path,caps={'meta':50,'claude':10},initial_holds={'meta':12,'claude':2})
        with mock.patch.object(prover.urllib.request,'urlopen',return_value=self.response()):
            self.call()
        status=BudgetLedger(self.path).status()['providers']
        self.assertEqual(status['meta']['cap_usd'],'50')
        self.assertEqual(status['meta']['external_hold_usd'],'12')
        self.assertEqual(status['claude']['external_hold_usd'],'2')

    def test_missing_negative_boolean_usage_retains_reservation(self):
        for bad in (None, {'prompt_tokens':-1,'completion_tokens':1},
                    {'prompt_tokens':True,'completion_tokens':1}):
            with self.subTest(usage=bad):
                with mock.patch.object(prover.urllib.request,'urlopen',return_value=self.response(bad)):
                    self.call()
        status=BudgetLedger(self.path).status()
        self.assertEqual(status['providers']['meta']['pending_count'],3)
        self.assertTrue(all(row['actual_usd'] is None for row in status['reservations']))

    def test_transport_failure_retains_reservation(self):
        with mock.patch.object(prover.urllib.request,'urlopen',side_effect=urllib.error.URLError('offline')):
            with self.assertRaises(prover.ApiError): self.call()
        self.assertEqual(BudgetLedger(self.path).status()['providers']['meta']['pending_count'],1)

    def test_bad_response_retains_reservation(self):
        with mock.patch.object(prover.urllib.request,'urlopen',return_value=io.BytesIO(b'not JSON')):
            with self.assertRaises(prover.ApiError): self.call()
        self.assertEqual(BudgetLedger(self.path).status()['providers']['meta']['pending_count'],1)

    def test_overrun_records_actual_and_reports_error(self):
        with mock.patch.object(prover.urllib.request,'urlopen',return_value=self.response({'prompt_tokens':100000,'completion_tokens':1})):
            with self.assertRaisesRegex(prover.ApiError,'settlement failed'):
                self.call()
        row=BudgetLedger(self.path).status()['reservations'][0]
        self.assertEqual(row['status'],'settled')
        self.assertEqual(Decimal(row['actual_usd']),Decimal('0.40002'))

    def test_injected_opener_does_not_create_real_ledger(self):
        result=self.call(opener=lambda *a,**kw:self.response())
        self.assertEqual(result.content,'rfl')
        self.assertFalse(self.path.exists())

    def test_invalid_token_limit_cannot_enter_transport(self):
        with mock.patch.object(prover.urllib.request,'urlopen') as transport:
            for bad in (True,1.5,-1):
                with self.assertRaises(prover.ApiError):
                    prover.chat_completion(model='muse-wonder-1.0',messages=[],api_key='offline-test-placeholder',max_tokens=bad)
            transport.assert_not_called()


    def test_null_and_empty_answers_settle_valid_usage_without_reasoning_disclosure(self):
        for content in (None, '', '   '):
            with self.subTest(content=content):
                payload = {'choices':[{'message':{'content':content, 'reasoning_content':'hidden-sentinel'},
                                       'finish_reason':'length'}],
                           'usage':{'prompt_tokens':10,'completion_tokens':100,
                                    'completion_tokens_details':{'reasoning_tokens':100}}}
                with mock.patch.object(prover.urllib.request,'urlopen',return_value=io.BytesIO(json.dumps(payload).encode())):
                    result=self.call()
                self.assertTrue(result.incomplete)
                self.assertEqual(result.finish_reason,'length')
                self.assertEqual(result.usage['reasoning_tokens'],100)
                self.assertNotIn('hidden-sentinel',json.dumps(vars(result)))
        rows=BudgetLedger(self.path).status()['reservations']
        self.assertEqual(len(rows),3)
        self.assertTrue(all(row['status']=='settled' and Decimal(row['actual_usd'])==Decimal('0.00204') for row in rows))

    def test_null_with_unknown_usage_retains_reservation(self):
        for usage in (None, {'prompt_tokens':-1,'completion_tokens':100}, {'prompt_tokens':10,'completion_tokens':True}):
            with mock.patch.object(prover.urllib.request,'urlopen',return_value=self.response(usage, None, 'length')):
                self.assertTrue(self.call().incomplete)
        self.assertEqual(BudgetLedger(self.path).status()['providers']['meta']['pending_count'],3)

    def test_malformed_content_and_finish_types_remain_pending(self):
        usage={'prompt_tokens':10,'completion_tokens':20}
        for content, finish in (([], 'stop'), ({}, 'stop'), (True,'stop'), ('rfl',[]), ('rfl',{}), ('rfl',True)):
            with self.subTest(content=content,finish=finish), mock.patch.object(prover.urllib.request,'urlopen',return_value=self.response(usage,content,finish)):
                with self.assertRaises(prover.ApiError):
                    self.call()
        self.assertEqual(BudgetLedger(self.path).status()['providers']['meta']['pending_count'],6)

    def test_nonempty_length_and_unknown_reason_are_incomplete(self):
        for reason in ('length', 'unknown-secret-sentinel'):
            with mock.patch.object(prover.urllib.request,'urlopen',return_value=self.response({'prompt_tokens':10,'completion_tokens':20},'rfl',reason)):
                result=self.call()
            self.assertTrue(result.incomplete)
            self.assertEqual(result.finish_reason,'length' if reason=='length' else 'unknown')
            self.assertNotIn('unknown-secret-sentinel',json.dumps(vars(result)))

    def test_empty_overrun_records_actual_and_fails_closed(self):
        with mock.patch.object(prover.urllib.request,'urlopen',return_value=self.response({'prompt_tokens':100000,'completion_tokens':1},None,'length')):
            with self.assertRaisesRegex(prover.ApiError,'settlement failed'):
                self.call()
        self.assertEqual(BudgetLedger(self.path).status()['reservations'][0]['status'],'settled')

    def test_research_headroom_reserved_before_transport(self):
        def transport(request,**kwargs):
            payload=json.loads(request.data)
            self.assertEqual(payload['max_tokens'],32768)
            self.assertNotIn('research_mode',payload)
            row=BudgetLedger(self.path).status()['reservations'][0]
            bound=(Decimal(len(request.data)+4096)*4+Decimal(32768)*20)/1_000_000
            self.assertEqual(Decimal(row['reserved_usd']),bound)
            return self.response({'prompt_tokens':10,'completion_tokens':32768},None,'length')
        with mock.patch.object(prover.urllib.request,'urlopen',side_effect=transport):
            result=self.call(max_tokens=32768,research_mode=True)
        self.assertTrue(result.incomplete)
        self.assertEqual(BudgetLedger(self.path).status()['providers']['meta']['settled_count'],1)

    def test_research_opt_in_is_strict_and_catalog_cap_unchanged(self):
        self.assertEqual(prover.MAX_TOKENS_LIMIT,16384)
        invalid=[{'max_tokens':16385},{'max_tokens':32769,'research_mode':True}]
        invalid += [{'research_mode':value} for value in (1,0,'true',None,[])]
        with mock.patch.object(prover.urllib.request,'urlopen') as transport:
            for options in invalid:
                with self.subTest(options=options), self.assertRaises(prover.ApiError):
                    self.call(**options)
            transport.assert_not_called()
        with self.assertRaises(ValueError):
            prover.prove_theorem('nat_add_zero',max_tokens=32768,log_path=None)
        import argparse
        parser=argparse.ArgumentParser()
        prover._add_common(parser)
        with mock.patch('sys.stderr',io.StringIO()), self.assertRaises(SystemExit):
            parser.parse_args(['--max-tokens','32768'])

    def test_catalog_records_incomplete_usage_without_checker_or_retry(self):
        for raw in (prover.ApiResult('rfl',{'input_tokens':10,'output_tokens':100},finish_reason='length',incomplete=True),
                    {'content':'rfl','usage':{'input_tokens':10,'output_tokens':100},'finish_reason':'length','incomplete':True}):
            client=mock.Mock(return_value=raw)
            checker=mock.Mock(return_value=prover.VerificationResult(True,'verified'))
            result=prover.prove_theorem('nat_add_zero',client_fn=client,checker_fn=checker,log_path=None,
                                       input_rate_per_mtok=4,output_rate_per_mtok=20)
            self.assertFalse(result['verified'])
            self.assertEqual(result['attempt_count'],1)
            self.assertEqual(result['usage_totals']['output_tokens'],100)
            self.assertEqual(result['cost_usd'],0.00204)
            self.assertTrue(result['attempts'][0]['incomplete'])
            checker.assert_not_called()
            client.assert_called_once()


    def test_benchmark_stops_after_incomplete_without_next_theorem_call(self):
        client=mock.Mock(return_value=prover.ApiResult('',{'input_tokens':10,'output_tokens':100},
                                                     finish_reason='length',incomplete=True))
        checker=mock.Mock()
        result=prover.run_benchmark(['nat_add_zero','nat_add_comm'],client_fn=client,
                                    checker_fn=checker,log_path=None)
        self.assertEqual(len(result['runs']),1)
        self.assertFalse(result['runs'][0]['verified'])
        client.assert_called_once()
        checker.assert_not_called()


if __name__=='__main__': unittest.main()
