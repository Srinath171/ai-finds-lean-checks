import concurrent.futures
import errno
import os
from unittest import mock
from decimal import Decimal
import json
import multiprocessing
from pathlib import Path
import tempfile
import threading
import unittest

from budget import BudgetLedger, BudgetError, BudgetExceeded, BudgetOverrun, LedgerCorrupt, LedgerLocked


def _process_reserve(path):
    ledger = BudgetLedger(path, lock_timeout=15)
    try:
        ledger.reserve('meta', '1')
        return True
    except BudgetExceeded:
        return False


class BudgetTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='budget-test-', dir=Path(__file__).resolve().parent)
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name) / 'budget.json'

    def test_reserve_settle_restart_and_external_hold(self):
        ledger = BudgetLedger(self.path, initial_holds={'meta':25})
        rid = ledger.reserve('meta', '1.25', purpose='test')
        self.assertEqual(Decimal(ledger.status()['providers']['meta']['committed_usd']), Decimal('26.25'))
        reopened = BudgetLedger(self.path)
        self.assertEqual(reopened.status()['providers']['meta']['pending_count'], 1)
        reopened.settle(rid, '.10')
        reopened.settle(rid, '.10')
        self.assertEqual(Decimal(ledger.status()['providers']['meta']['committed_usd']), Decimal('25.10'))
        with self.assertRaises(BudgetError):
            reopened.settle(rid, '.01')
        with self.assertRaises(BudgetError):
            BudgetLedger(self.path, initial_holds={'meta':0})

    def test_unknown_or_crashed_request_retains_reservation(self):
        ledger = BudgetLedger(self.path, caps={'meta':2,'claude':3})
        ledger.reserve('meta',2)
        with self.assertRaises(BudgetExceeded):
            BudgetLedger(self.path).reserve('meta','.000001')
        BudgetLedger(self.path).reserve('claude',3)

    def test_invalid_amounts_and_caps(self):
        ledger = BudgetLedger(self.path)
        for bad in [-1, float('nan'), float('inf'), '-Infinity', True, None]:
            with self.subTest(bad=bad):
                with self.assertRaises(ValueError): ledger.reserve('meta',bad)
                with self.assertRaises(ValueError): ledger.settle('missing',bad)
        for bad in [0,-1,True,float('nan')]:
            with self.assertRaises(ValueError): BudgetLedger(self.path,caps={'meta':bad,'claude':40})
        with self.assertRaises(ValueError): ledger.reserve('other',1)
        with self.assertRaises(ValueError): ledger.reserve('meta',0)

    def test_measured_overrun_is_recorded_and_blocks_further_spend(self):
        ledger=BudgetLedger(self.path,caps={'meta':2,'claude':3})
        rid=ledger.reserve('meta',1)
        with self.assertRaises(BudgetOverrun): ledger.settle(rid,3)
        self.assertTrue(ledger.status()['providers']['meta']['over_cap'])
        with self.assertRaises(BudgetExceeded): ledger.reserve('meta','.1')

    def test_threads_cannot_oversubscribe(self):
        BudgetLedger(self.path,caps={'meta':5,'claude':1})
        with concurrent.futures.ThreadPoolExecutor(max_workers=10) as pool:
            accepted=list(pool.map(_process_reserve,[str(self.path)]*20))
        self.assertEqual(sum(accepted),5)
        self.assertEqual(BudgetLedger(self.path).status()['providers']['meta']['pending_count'],5)

    def test_same_process_threads_do_not_overlap_file_lock_lifecycle(self):
        ledger=BudgetLedger(self.path)
        entered=threading.Event()
        allow_release=threading.Event()
        second_finished=threading.Event()
        real_open=os.open
        lock_opens=[]
        def observe_open(path, flags, *args, **kwargs):
            if Path(path)==ledger.lock_path:
                lock_opens.append(threading.get_ident())
            return real_open(path,flags,*args,**kwargs)
        def owner():
            with ledger._locked():
                entered.set()
                self.assertTrue(allow_release.wait(2))
        def contender():
            ledger.status()
            second_finished.set()
        with mock.patch('budget.os.open',side_effect=observe_open):
            with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
                first=pool.submit(owner)
                self.assertTrue(entered.wait(2))
                second=pool.submit(contender)
                self.assertFalse(second_finished.wait(.05))
                self.assertEqual(len(lock_opens),1)
                allow_release.set()
                first.result(timeout=2)
                second.result(timeout=2)
        self.assertEqual(len(lock_opens),2)

    def test_transient_windows_replace_denial_retries_under_lock(self):
        ledger=BudgetLedger(self.path)
        real_replace=os.replace
        calls=[]
        def replacing(src,dest):
            calls.append(1)
            self.assertTrue(ledger.lock_path.exists())
            if len(calls)==1:
                error=PermissionError(errno.EACCES,'delete pending',str(dest))
                error.winerror=5
                raise error
            return real_replace(src,dest)
        with mock.patch('budget.os.replace',side_effect=replacing):
            ledger.reserve('meta',1)
        self.assertEqual(len(calls),2)
        self.assertEqual(ledger.status()['providers']['meta']['pending_count'],1)

    def test_persistent_replace_denial_preserves_original_ledger(self):
        ledger=BudgetLedger(self.path,lock_timeout=.03)
        before=self.path.read_bytes()
        error=PermissionError(errno.EACCES,'persistent deny',str(self.path))
        error.winerror=5
        with mock.patch('budget.os.replace',side_effect=error):
            with self.assertRaises(PermissionError): ledger.reserve('meta',1)
        self.assertEqual(self.path.read_bytes(),before)
        self.assertEqual(ledger.status()['providers']['meta']['pending_count'],0)

    def test_access_denied_with_existing_lock_waits_without_spending(self):
        ledger=BudgetLedger(self.path, lock_timeout=.03)
        lock=ledger.lock_path
        lock.write_text('{"token":"other-owner"}')
        denied=PermissionError(errno.EACCES, 'Access denied', str(lock))
        before=self.path.read_bytes()
        with mock.patch('budget.os.open', side_effect=denied):
            with self.assertRaises(LedgerLocked): ledger.reserve('meta',1)
        self.assertTrue(lock.exists())
        self.assertEqual(self.path.read_bytes(),before)

    def test_access_denied_after_observed_collision_recovers(self):
        ledger=BudgetLedger(self.path)
        real_open=os.open
        attempts=[]
        def colliding_open(path, flags, *args, **kwargs):
            if Path(path) == ledger.lock_path:
                attempts.append(1)
                if len(attempts)==1:
                    raise FileExistsError(errno.EEXIST, 'competing lock', str(path))
                if len(attempts)==2:
                    raise PermissionError(errno.EACCES, 'delete pending', str(path))
            return real_open(path, flags, *args, **kwargs)
        with mock.patch('budget.os.open', side_effect=colliding_open):
            ledger.reserve('meta',1)
        self.assertEqual(len(attempts),3)
        self.assertEqual(ledger.status()['providers']['meta']['pending_count'],1)

    def test_windows_sharing_violation_without_visible_lock_recovers(self):
        ledger=BudgetLedger(self.path)
        real_open=os.open
        attempts=[]
        def colliding_open(path, flags, *args, **kwargs):
            if Path(path) == ledger.lock_path:
                attempts.append(1)
                if len(attempts)==1:
                    error=PermissionError(errno.EACCES, 'sharing violation', str(path))
                    error.winerror=32
                    raise error
            return real_open(path, flags, *args, **kwargs)
        with mock.patch('budget.os.open', side_effect=colliding_open):
            ledger.reserve('meta',1)
        self.assertEqual(len(attempts),2)
        self.assertEqual(ledger.status()['providers']['meta']['pending_count'],1)

    def test_genuine_permission_denial_is_not_retried(self):
        ledger=BudgetLedger(self.path)
        before=self.path.read_bytes()
        denied=PermissionError(errno.EACCES, 'directory ACL denies write', str(ledger.lock_path))
        with mock.patch('budget.os.open', side_effect=denied) as opened:
            with self.assertRaises(PermissionError): ledger.reserve('meta',1)
        self.assertEqual(opened.call_count,1)
        self.assertEqual(self.path.read_bytes(),before)
        self.assertFalse(ledger.lock_path.exists())

    def test_processes_cannot_oversubscribe(self):
        BudgetLedger(self.path,caps={'meta':5,'claude':1})
        with concurrent.futures.ProcessPoolExecutor(max_workers=4,mp_context=multiprocessing.get_context('spawn')) as pool:
            accepted=list(pool.map(_process_reserve,[str(self.path)]*12))
        self.assertEqual(sum(accepted),5)
        self.assertEqual(BudgetLedger(self.path).status()['providers']['meta']['pending_count'],5)

    def test_stale_lock_fails_closed_and_is_not_removed(self):
        BudgetLedger(self.path)
        lock=self.path.with_name('budget.json.lock')
        lock.write_text('{"token":"stale","pid":999999,"created_at":"2000-01-01"}')
        with self.assertRaises(LedgerLocked): BudgetLedger(self.path,lock_timeout=.03)
        self.assertTrue(lock.exists())

    def test_malformed_ledger_fails_closed(self):
        for content in ['{broken', '{}', 'null', '{"version":1,"created_at":"now","caps_usd":null,"initial_holds_usd":{},"reservations":[]}']:
            self.path.write_text(content)
            with self.assertRaises(LedgerCorrupt): BudgetLedger(self.path)
            self.assertEqual(self.path.read_text(),content)

    def test_invalid_record_fails_closed(self):
        ledger=BudgetLedger(self.path)
        ledger.reserve('meta',1)
        state=json.loads(self.path.read_text())
        state['reservations'][0]['reserved_usd']='NaN'
        self.path.write_text(json.dumps(state))
        with self.assertRaises(LedgerCorrupt): ledger.status()

    def test_decimal_accounting_does_not_round_under(self):
        ledger=BudgetLedger(self.path,caps={'meta':'.3','claude':1})
        for _ in range(3): ledger.reserve('meta','.1')
        self.assertEqual(ledger.status()['providers']['meta']['available_usd'],'0')
        with self.assertRaises(BudgetExceeded): ledger.reserve('meta','0.0000000001')


if __name__=='__main__': unittest.main()
