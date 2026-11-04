"""Offline regressions for the local verifier audit; no model/key access."""
import hashlib
import os
import subprocess
import sys
import tempfile
import time
import unittest
from datetime import datetime
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import prover


class AxiomAuditTests(unittest.TestCase):
    def test_suffix_cannot_hide_disallowed_axiom(self):
        report = "not_x does not depend on any axioms\nx depends on axioms: [BadAxiom]"
        self.assertEqual(prover.parse_axioms_output(report, 'x'), {'BadAxiom'})
        self.assertIsNone(prover.parse_axioms_output('not_x does not depend on any axioms', 'x'))

    def test_duplicate_conflicting_and_trailing_reports_rejected(self):
        for text in (
            "'x' does not depend on any axioms\n'x' depends on axioms: [BadAxiom]",
            "x does not depend on any axioms\nx does not depend on any axioms",
            "prefix x does not depend on any axioms",
            "x does not depend on any axioms trailing text",
            "x depends on axioms: [propext,]",
            "x depends on axioms: [propext, propext]",
        ):
            with self.subTest(text=text):
                self.assertIsNone(prover.parse_axioms_output(text, 'x'))

    def test_multiline_exact_report(self):
        text = "diagnostic\n'x' depends on axioms: [propext,\n Quot.sound]\n"
        self.assertEqual(prover.parse_axioms_output(text, 'x'), {'propext', 'Quot.sound'})

    def test_checker_rejects_suffix_report(self):
        theorem = prover.get_theorem('nat_add_zero')
        runner = lambda command, **kw: subprocess.CompletedProcess(command, 0, "not_nat_add_zero does not depend on any axioms", '')
        result = prover.check_proof(theorem, 'rfl', runner=runner)
        self.assertFalse(result.verified)
        self.assertEqual(result.status, 'checker_error')


class UsageAuditTests(unittest.TestCase):
    def test_exact_nonnegative_usage_only(self):
        for bad in (-1, True, False, 1.5, '12', None):
            with self.subTest(bad=bad):
                result = prover._normalize_usage({'prompt_tokens': bad, 'completion_tokens': bad})
                self.assertIsNone(result['input_tokens'])
                self.assertIsNone(result['output_tokens'])
                self.assertIsNone(prover._estimate_cost_usd({'input_tokens': bad, 'output_tokens': bad}, 4, 20))
        self.assertEqual(prover._normalize_usage({'prompt_tokens': 0, 'completion_tokens': 12})['input_tokens'], 0)

    def test_malformed_injected_usage_keeps_reservation(self):
        client = lambda **kw: prover.ApiResult('rfl', {'input_tokens': -1, 'output_tokens': 0})
        checker = lambda *a, **kw: prover.VerificationResult(True, 'verified', axioms=[])
        result = prover.prove_theorem('nat_add_zero', client_fn=client, checker_fn=checker,
                                     budget_usd=1, input_rate_per_mtok=4,
                                     output_rate_per_mtok=20, log_path=None)
        self.assertIsNone(result['cost_usd'])
        self.assertGreater(result['reserved_or_measured_usd'], 0)


class ProcessAuditTests(unittest.TestCase):
    def test_capture_is_bounded_during_execution(self):
        started = time.monotonic()
        with self.assertRaises(prover.OutputLimitExceeded):
            prover._run_bounded([sys.executable, '-c', "import sys,time; sys.stdout.buffer.write(b'x'*2000000); sys.stdout.flush(); time.sleep(30)"],
                                cwd=None, env=prover._sanitized_env(), timeout=5,
                                max_output_bytes=4096)
        self.assertLess(time.monotonic()-started, 6)

    def test_timeout_stops_launched_process(self):
        launched=[]
        real_popen=subprocess.Popen
        def capture(*args, **kwargs):
            p=real_popen(*args, **kwargs)
            launched.append(p)
            return p
        with mock.patch.object(prover.subprocess, 'Popen', side_effect=capture):
            with self.assertRaises(subprocess.TimeoutExpired):
                prover._run_bounded([sys.executable, '-c', 'import time; time.sleep(30)'],
                                    cwd=None, env=prover._sanitized_env(), timeout=0.15)
        self.assertIsNotNone(launched[0].poll())

    def test_successful_capture(self):
        result=prover._run_bounded([sys.executable,'-c',"print('ok')"],cwd=None,
                                  env=prover._sanitized_env(),timeout=3,max_output_bytes=64)
        self.assertEqual(result.returncode,0)
        self.assertEqual(result.stdout.strip(),'ok')

    @unittest.skipUnless(os.name=='nt','Windows process-tree termination')
    def test_timeout_stops_descendant_process(self):
        import ctypes
        from ctypes import wintypes
        with tempfile.TemporaryDirectory() as tmp:
            pid_path=Path(tmp)/'child.pid'
            program=("import subprocess,sys,time,pathlib; "
                     "p=subprocess.Popen([sys.executable,'-c','import time; time.sleep(30)']); "
                     f"pathlib.Path({str(pid_path)!r}).write_text(str(p.pid)); time.sleep(30)")
            with self.assertRaises(subprocess.TimeoutExpired):
                prover._run_bounded([sys.executable,'-c',program],cwd=None,
                                    env=prover._sanitized_env(),timeout=1)
            self.assertTrue(pid_path.exists(),'child was started before timeout')
            pid=int(pid_path.read_text())
            kernel=ctypes.WinDLL('kernel32',use_last_error=True)
            kernel.OpenProcess.argtypes=(wintypes.DWORD,wintypes.BOOL,wintypes.DWORD)
            kernel.OpenProcess.restype=wintypes.HANDLE
            kernel.WaitForSingleObject.argtypes=(wintypes.HANDLE,wintypes.DWORD)
            kernel.CloseHandle.argtypes=(wintypes.HANDLE,)
            handle=kernel.OpenProcess(0x100000,False,pid)
            if handle:
                try: self.assertEqual(kernel.WaitForSingleObject(handle,0),0,'child survived timeout')
                finally: kernel.CloseHandle(handle)
            else:
                self.assertEqual(ctypes.get_last_error(),87,'child query failed unexpectedly')

    def test_checker_output_cap_fails_closed(self):
        runner=lambda command, **kw: subprocess.CompletedProcess(command,0,'x'*(prover.MAX_LEAN_OUTPUT_CHARS+1),'')
        result=prover.check_proof(prover.get_theorem('nat_add_zero'),'rfl',runner=runner)
        self.assertFalse(result.verified)
        self.assertEqual(result.status,'checker_error')


class ReplayAuditTests(unittest.TestCase):
    def test_candidate_hash_matches_exact_source(self):
        theorem=prover.get_theorem('nat_add_zero')
        captured=[]
        def runner(command,**kw):
            captured.append(Path(command[-1]).read_bytes())
            return subprocess.CompletedProcess(command,0,"'nat_add_zero' does not depend on any axioms",'')
        result=prover.check_proof(theorem,'by\n  rfl',runner=runner)
        expected=hashlib.sha256(prover.build_candidate_source(theorem,'rfl').encode('utf-8')).hexdigest()
        self.assertEqual(result.candidate_source_sha256,expected)
        self.assertEqual(result.candidate_source_sha256,hashlib.sha256(captured[0]).hexdigest())
        self.assertEqual(result.to_dict()['candidate_source_sha256'],expected)

    def test_started_at_precedes_request_and_finish(self):
        calls=[]
        def client(**kw):
            calls.append(datetime.now(prover.timezone.utc))
            time.sleep(0.02)
            return prover.ApiResult('rfl')
        checker=lambda *a,**kw: prover.VerificationResult(True,'verified',axioms=[],candidate_source_sha256='abc')
        result=prover.prove_theorem('nat_add_zero',client_fn=client,checker_fn=checker,log_path=None)
        self.assertLessEqual(datetime.fromisoformat(result['started_at']),calls[0])
        self.assertGreater(datetime.fromisoformat(result['finished_at']),calls[0])
        self.assertEqual(result['attempts'][0]['candidate_source_sha256'],'abc')

if __name__=='__main__': unittest.main()
