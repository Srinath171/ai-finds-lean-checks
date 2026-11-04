"""Real Lean integration tests; kept separate from mocked unit tests."""
import sys
import unittest
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
import prover

class LiveLeanTests(unittest.TestCase):
    @unittest.skipUnless(prover._lean_invocation(Path('candidate.lean')), 'Lean not installed')
    def test_all_catalog_fixtures(self):
        for theorem in prover.load_catalog():
            with self.subTest(theorem=theorem.id):
                result=prover.check_proof(theorem,prover.DEMO_PROOFS[theorem.id],timeout=25)
                self.assertTrue(result.verified,result.diagnostics)
                self.assertNotIn('Lean.ofReduceBool',result.axioms)

    @unittest.skipUnless(prover._lean_invocation(Path('candidate.lean')), 'Lean not installed')
    def test_false_statement_rejected_by_real_kernel(self):
        theorem=prover.Theorem('false_claim','false_claim','theorem false_claim : 1 = 2','decide')
        self.assertFalse(prover.check_proof(theorem,'rfl',timeout=25).verified)
        self.assertFalse(prover.check_proof(theorem,'decide',timeout=25).verified)

    def test_budget_reserves_before_network(self):
        calls=[]
        def client(**kwargs):
            calls.append(1)
            raise AssertionError('Budget should prevent call')
        r=prover.prove_theorem('prop_id',budget_usd=0.001,input_rate_per_mtok=4,output_rate_per_mtok=20,client_fn=client,log_path=None)
        self.assertEqual(r['status'],'budget_exceeded')
        self.assertEqual(calls,[])

    def test_native_axiom_rejected(self):
        from types import SimpleNamespace
        t=prover.get_theorem('nat_add_zero')
        runner=lambda *a,**kw: SimpleNamespace(returncode=0,stdout="'nat_add_zero' depends on axioms: [Lean.ofReduceBool]",stderr='')
        self.assertFalse(prover.check_proof(t,'rfl',runner=runner).verified)

if __name__=='__main__': unittest.main()
