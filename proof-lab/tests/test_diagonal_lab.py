"""Durable tests for frontier/diagonal_lab.py. Stdlib unittest only."""
import copy, importlib.util, json, sys, unittest
from pathlib import Path
from unittest import mock
ROOT = Path(__file__).resolve().parent.parent
_spec = importlib.util.spec_from_file_location("diagonal_lab", ROOT/"frontier"/"diagonal_lab.py")
dl = importlib.util.module_from_spec(_spec); sys.modules["diagonal_lab"] = dl; _spec.loader.exec_module(dl)

def bool_eval(n, gates, out, a):
    sig=[bool((a>>i)&1) for i in range(n)]
    for i,j in gates: sig.append(not (sig[i] and sig[j]))
    return int(sig[out])
def lexkey(m,n): return tuple((m>>a)&1 for a in range(1<<n))
def oracle_missing(n,s):
    comp={dl.evaluate_mask(n,d) for d in dl.enumerate_descriptions(n,s)}
    for m in sorted(range(1<<(1<<n)), key=lambda x: lexkey(x,n)):
        if m not in comp: return m
    return None

class TestCountsAndCaps(unittest.TestCase):
    def test_exact_count_vs_enumeration(self):
        for n,s in [(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)]:
            with self.subTest(n=n,s=s):
                ds=dl.enumerate_descriptions(n,s)
                self.assertEqual(len(ds), dl.description_count(n,s))
                self.assertEqual(len(set(ds)), len(ds))  # no duplicate descriptions
                for d in ds:
                    self.assertTrue(0 <= d.output < n+len(d.gates))
                    for k,(i,j) in enumerate(d.gates): self.assertTrue(0<=i<n+k and 0<=j<n+k)
        self.assertEqual(dl.description_count(2,3),3038)
        self.assertEqual(dl.description_count(3,2),759)
        self.assertEqual(dl.description_count(3,4),929559)
        self.assertEqual(dl.description_count(3,3),22359)
        self.assertEqual(len(dl.enumerate_descriptions(3,3)),22359)
    def test_refused_before_enumeration(self):
        self.assertEqual(dl.run_experiment(3,4)["status"],"REFUSED")
        self.assertEqual(dl.run_experiment(3,4)["missing_status"],dl.UNKNOWN)
        self.assertEqual(dl.run_experiment(3,4)["num_descriptions_enumerated"],0)
        with self.assertRaises(dl.DescriptionCapExceeded): dl.enumerate_descriptions(2,3,max_descriptions=100)
        with self.assertRaises(ValueError): dl.enumerate_descriptions(3,4,max_descriptions=100000)
    def test_invalid_params(self):
        for bad in [(0,1),(4,1),(1,5),(1,-1),(True,1),(1,1.5),(2.0,1)]:
            with self.assertRaises(ValueError): dl.run_experiment(*bad)
        for bad in [0,-1,True,1.5,"10"]:
            with self.assertRaises(ValueError): dl.run_experiment(2,2,max_descriptions=bad)

class TestMissing(unittest.TestCase):
    def test_n2s3_xor6(self):
        r=dl.run_experiment(2,3); self.assertEqual((r["status"],r["missing_mask"]),("OK",6))
        self.assertEqual(r["missing_truth_vector"],[0,1,1,0]); self.assertEqual(r["num_distinct_computed"],13)
        self.assertNotIn(6,{dl.evaluate_mask(2,d) for d in dl.enumerate_descriptions(2,3)})
    def test_lex_mex_vs_oracle_and_n1_n3(self):
        for n,s in [(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)]:
            with self.subTest(n=n,s=s): self.assertEqual(dl.run_experiment(n,s)["missing_mask"],oracle_missing(n,s))
        self.assertEqual(dl.run_experiment(3,2)["missing_mask"],0)
        self.assertEqual(dl.run_experiment(3,3)["missing_mask"],128)
        self.assertEqual(dl.run_experiment(1,3)["status"],"NO_MISSING")
        self.assertIsNone(dl.run_experiment(1,4)["missing_mask"])
        self.assertEqual(dl.mex([0,1,3]),2); self.assertEqual(dl.mex_sorted([0,1,3]),2)
    def test_bool_vs_mask(self):
        for d in dl.enumerate_descriptions(2,2):
            m=dl.evaluate_mask(2,d)
            for a in range(4): self.assertEqual(bool_eval(2,d.gates,d.output,a),(m>>a)&1)

class TestCertificates(unittest.TestCase):
    @classmethod
    def setUpClass(cls): cls.cert=dl.build_certificate(2,3)
    def test_valid_and_metrics(self):
        self.assertTrue(dl.verify_certificate(self.cert))
        d=dl.verify_certificate_detailed(self.cert); self.assertTrue(d["valid"]); self.assertEqual(d["rows_checked"],3038)
        met=dl.certificate_metrics(self.cert); self.assertEqual(met["num_descriptions"],3038)
        self.assertEqual(met["truth_table_bits"],4)
        self.assertEqual(met["certificate_bytes"],len(dl.canonical_json_bytes(self.cert)))
        self.assertEqual(met["checker_gate_operations"],sum(len(x.gates) for x in dl.enumerate_descriptions(2,3)))
        self.assertEqual(met["checker_literal_operations"],2*met["checker_gate_operations"])
        for row in self.cert["rows"]:  # independent re-evaluation
            gates=[tuple(g) for g in row["gates"]]
            self.assertNotEqual(bool_eval(2,gates,row["output"],row["assignment"]),row["target_output"])
    def test_corrupt_rejected(self):
        def bad(mut):
            c=copy.deepcopy(self.cert); mut(c); return c
        cases=[
            lambda c: c["rows"].pop(), lambda c: c["rows"].append(copy.deepcopy(c["rows"][0])),
            lambda c: c["rows"].__setitem__(1,copy.deepcopy(c["rows"][0])),
            lambda c: c["rows"][0].__setitem__("assignment",0 if c["rows"][0]["assignment"]!=0 else 1),
            lambda c: c["rows"][0].__setitem__("circuit_output",1-c["rows"][0]["circuit_output"]),
            lambda c: c["rows"][0].__setitem__("gates",[[0,0]]), lambda c: c["rows"][0].__setitem__("output",1),
            lambda c: c["rows"][0].__setitem__("assignment",True), lambda c: c["rows"][0].__setitem__("id",1.0),
            lambda c: c["rows"][0].__setitem__("extra",1), lambda c: c.__setitem__("target_mask",7),
            lambda c: c.__setitem__("rows",c["rows"][:-1]), lambda c: c.__setitem__("rows",{}),
            lambda c: c.pop("rows"),
        ]
        # fix agreeing-assignment case: choose an assignment that agrees if the first mutation is not one
        for i,mut in enumerate(cases):
            with self.subTest(case=i): self.assertFalse(dl.verify_certificate(bad(mut)))
        self.assertFalse(dl.verify_certificate(None)); self.assertFalse(dl.verify_certificate({}))
    def test_strict_numeric_metadata(self):
        for builder, verifier in [
                (dl.build_certificate, dl.verify_certificate),
                (dl.build_grouped_certificate, dl.verify_grouped_certificate)]:
            cert = builder(1, 0)
            keys = ["num_descriptions", "truth_table_bits"]
            keys.append("num_functions_universe" if "rows" in cert
                        else "num_distinct_computed")
            for key in keys:
                with self.subTest(kind=cert["kind"], key=key):
                    bad = copy.deepcopy(cert); bad[key] = float(bad[key])
                    self.assertFalse(verifier(bad))
            bad = copy.deepcopy(cert); bad["num_descriptions"] = True
            self.assertFalse(verifier(bad))
            for vector in [[False, False], [0.0, 0.0]]:
                bad = copy.deepcopy(cert); bad["target_truth_vector"] = vector
                self.assertFalse(verifier(bad))
            if "num_distinct_computed" in cert:
                bad = copy.deepcopy(cert); bad["num_distinct_computed"] = True
                self.assertFalse(verifier(bad))

    def test_validity_means_missing_not_lexicographically_first(self):
        # At n=2,s=0 both 0 and 1 are missing; only 0 is lex-first.
        self.assertEqual(dl.run_experiment(2, 0)["missing_mask"], 0)
        for builder, verifier in [
                (dl.build_certificate, dl.verify_certificate),
                (dl.build_grouped_certificate, dl.verify_grouped_certificate)]:
            self.assertTrue(verifier(builder(2, 0, target_mask=1)))
            with self.assertRaises(ValueError):
                builder(2, 0, target_mask=10)  # x0 is computed

    def test_partial_coverage_counterexample(self):
        pc=dl.partial_coverage_counterexample()
        self.assertEqual(pc["omitted_descriptions_computing_target"][0]["gates"],[[0,1]])
        partial={"format":dl.CERT_FORMAT,"kind":"naive-per-circuit","n":2,"s":1,"target_mask":7,
                 "target_truth_vector":dl.truth_vector(7,2),"num_descriptions":dl.description_count(2,1),
                 "num_functions_universe":16,"truth_table_bits":4,
                 "rows":[{"id":i,"gates":[],"output":i,"assignment":0,"circuit_output":0,"target_output":1} for i in (0,1)]}
        self.assertFalse(dl.verify_certificate(partial))  # incomplete => rejects the false claim

class TestGrouping(unittest.TestCase):
    def test_grouped_valid_smaller_but_needs_coverage(self):
        g=dl.build_grouped_certificate(2,3); self.assertTrue(dl.verify_grouped_certificate(g))
        naive=dl.certificate_metrics(dl.build_certificate(2,3)); gm=dl.certificate_metrics(g)
        self.assertEqual((gm["num_rows"],naive["num_rows"]),(13,3038))
        self.assertLess(gm["certificate_bytes"],naive["certificate_bytes"])
        rows_only=copy.deepcopy(g)
        for grp in rows_only["groups"]: del grp["description_ids"]
        self.assertFalse(dl.verify_grouped_certificate(rows_only))  # no coverage => unsound, rejected
        badg=copy.deepcopy(g); badg["groups"][0]["description_ids"].pop()
        self.assertFalse(dl.verify_grouped_certificate(badg))
        badg2=copy.deepcopy(g); badg2["groups"][0]["description_ids"].append(badg2["groups"][1]["description_ids"][0])
        self.assertFalse(dl.verify_grouped_certificate(badg2))

    def test_duplicate_computed_masks_rejected_even_with_exact_id_coverage(self):
        cert = dl.build_grouped_certificate(2, 1)
        for group in cert["groups"]:
            if len(group["description_ids"]) > 1:
                split = copy.deepcopy(group)
                split["description_ids"] = [group["description_ids"].pop()]
                cert["groups"].append(split)
                break
        cert["num_distinct_computed"] = len(cert["groups"])
        ids = [rid for group in cert["groups"] for rid in group["description_ids"]]
        self.assertEqual(sorted(ids), list(range(dl.description_count(2, 1))))
        result = dl.verify_grouped_certificate_detailed(cert)
        self.assertFalse(result["valid"])
        self.assertIn("duplicate group computed_mask", result["reason"])

    def test_explicit_cap_reaches_grouped_metrics(self):
        cert = dl.build_grouped_certificate(2, 1)
        cap = dl.description_count(2, 1)
        with mock.patch.object(dl, "enumerate_descriptions",
                               wraps=dl.enumerate_descriptions) as enumerate_mock:
            dl.certificate_metrics(cert, max_descriptions=cap)
        enumerate_mock.assert_called_once_with(2, 1, cap)
        with mock.patch.object(dl, "certificate_metrics",
                               wraps=dl.certificate_metrics) as metrics_mock:
            result = dl.run_experiment(2, 1, max_descriptions=cap)
        self.assertEqual(result["status"], "OK")
        self.assertEqual(len(metrics_mock.call_args_list), 2)
        self.assertTrue(all(call.args[1] == cap
                            for call in metrics_mock.call_args_list))

class TestSavedExample(unittest.TestCase):
    def test_saved_json_verifies(self):
        p=ROOT/"frontier"/"results"/"diagonal-n2-s3.json"; self.assertTrue(p.exists())
        r=json.loads(p.read_text(encoding="utf-8"))
        self.assertEqual((r["n"],r["s"],r["missing_mask"],r["status"]),(2,3,6,"OK"))
        self.assertTrue(dl.verify_certificate(r["certificate"])); self.assertTrue(dl.verify_grouped_certificate(r["grouped_certificate"]))

if __name__=="__main__": unittest.main()
