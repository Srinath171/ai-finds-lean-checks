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
        self.tmp=tempfile.TemporaryDirectory()
        self.path=Path(self.tmp.name)/'spending.json'
        self.patch=mock.patch.object(prover,'SPENDING_LEDGER_PATH',self.path)
        self.patch.start()

    def tearDown(self):
        self.patch.stop()
        self.tmp.cleanup()

    def call(self, **kwargs):
        return prover.chat_completion(model='muse-wonder-1.0',
            messages=[{'role':'user','content':'Give a proof.'}],
            api_key='offline-test-placeholder',max_tokens=100,**kwargs)

    @staticmethod
    def response(usage=None):
        data={'choices':[{'message':{'content':'rfl'}}]}
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


if __name__=='__main__': unittest.main()
