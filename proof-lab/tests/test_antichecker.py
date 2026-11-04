"""Durable tests for frontier/antichecker.py. Stdlib unittest only."""
import copy, importlib.util, json, sys, unittest
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
_spec = importlib.util.spec_from_file_location("antichecker", ROOT/"frontier"/"antichecker.py")
ac = importlib.util.module_from_spec(_spec); sys.modules["antichecker"] = ac; _spec.loader.exec_module(ac)

EXPECTED = {(2,2):(0,2,[0,3],True),(2,4):(9,4,[0,1,2,3],True),(3,3):(128,4,[3,5,6,7],False)}

class TestRealMinima(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.saved = json.loads((ROOT/"frontier"/"results"/"antichecker.json").read_text(encoding="utf-8"))
    def test_saved_real_minima_and_checker(self):
        self.assertTrue(ac.verify_result(self.saved))
        for c in self.saved["cases"]:
            self.assertEqual((c["target_mask"],c["minimum_distinguishing_size"],c["minimum_distinguishing_set"],c["conjecture_holds_for_case"]), EXPECTED[(c["n"],c["s"])])
        self.assertFalse(self.saved["conjecture_holds_for_all_cases"])
        self.assertEqual(self.saved["counterexample_case"]["target_mask"],128)
    def test_forcing_witnesses_n3(self):
        c = [x for x in self.saved["cases"] if (x["n"],x["s"])==(3,3)][0]
        self.assertEqual({w["reachable_mask"]:w["forced_assignment"] for w in c["singleton_disagreement_witnesses"]}, {0:7,136:3,160:5,192:6})
        for A in ([3,5,6],[3,5,7],[5,6,7],[3,6,7]):
            self.assertFalse(ac.is_distinguishing(A, c["reachable_masks_lex_order"], 128, 3))

class TestRejection(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.saved = json.loads((ROOT/"frontier"/"results"/"antichecker.json").read_text(encoding="utf-8"))
    def test_partial_coverage_rejected(self):
        bad = copy.deepcopy(self.saved)
        bad["cases"][2]["reachable_masks_lex_order"].remove(0)  # omit const-0: partial coverage
        self.assertFalse(ac.verify_case_result(bad["cases"][2]))
        self.assertFalse(ac.verify_result(bad))
        # A set hitting only a partial reachable list need not hit the full list
        self.assertTrue(ac.is_distinguishing([3,5,6], [136,160,192], 128, 3))
        self.assertFalse(ac.is_distinguishing([3,5,6], self.saved["cases"][2]["reachable_masks_lex_order"], 128, 3))
    def test_malformed_test_sets_rejected(self):
        for badA in ([True,3],[3.0,5],[8],[-1],[3,3,5],[3,"5"],"3567",None,3):
            with self.assertRaises(ValueError): ac.validate_assignment_set(badA, 3)
            with self.assertRaises(ValueError): ac.is_distinguishing(badA, [0], 128, 3)
        bad = copy.deepcopy(self.saved); bad["cases"][2]["minimum_distinguishing_set"]=[3,3,5,6,7]
        self.assertFalse(ac.verify_case_result(bad["cases"][2]))
        bad2 = copy.deepcopy(self.saved); bad2["cases"][2]["minimum_distinguishing_set"]=[3,5,6]
        self.assertFalse(ac.verify_case_result(bad2["cases"][2]))  # agrees with target on const-0 witness
        bad3 = copy.deepcopy(self.saved); bad3["cases"][0]["minimum_distinguishing_size"]=1
        self.assertFalse(ac.verify_case_result(bad3["cases"][0]))

    def test_numeric_aliases_rejected(self):
        original = self.saved["cases"][0]
        for key in ("description_count_exact", "num_distinct_reachable"):
            with self.subTest(key=key):
                case = copy.deepcopy(original); case[key] = float(case[key])
                self.assertFalse(ac.verify_case_result(case))
        corruptions = [
            lambda c: c.__setitem__("reachable_masks_lex_order",
                                    [float(m) for m in c["reachable_masks_lex_order"]]),
            lambda c: c.__setitem__("target_truth_vector",
                                    [bool(v) for v in c["target_truth_vector"]]),
            lambda c: c.__setitem__("all_minimum_distinguishing_sets",
                                    [[float(j) for j in A]
                                     for A in c["all_minimum_distinguishing_sets"]]),
        ]
        for mutate in corruptions:
            case = copy.deepcopy(original); mutate(case)
            self.assertFalse(ac.verify_case_result(case))
        case = copy.deepcopy(self.saved["cases"][2])
        case["singleton_disagreement_witnesses"][0]["forced_assignment"] = 7.0
        self.assertFalse(ac.verify_case_result(case))
        result = copy.deepcopy(self.saved)
        result["conjecture_holds_for_all_cases"] = 0
        self.assertFalse(ac.verify_result(result))
        result = copy.deepcopy(self.saved)
        result["counterexample_case"]["minimum_distinguishing_size"] = 4.0
        self.assertFalse(ac.verify_result(result))

    def test_false_claim_labels_and_unexpected_schema_rejected(self):
        for key, value in [("conjecture", "P = NP"),
                           ("scope", "For every input length"),
                           ("model", {"gate": "AND; constants and complements are free"})]:
            with self.subTest(key=key):
                result = copy.deepcopy(self.saved); result[key] = value
                self.assertFalse(ac.verify_result(result))
        case = copy.deepcopy(self.saved["cases"][0]); case["lex_order"] = "numeric mask order"
        self.assertFalse(ac.verify_case_result(case))
        result = copy.deepcopy(self.saved); del result["scope"]
        self.assertFalse(ac.verify_result(result))
        result = copy.deepcopy(self.saved); result["p_vs_np_proved"] = True
        self.assertFalse(ac.verify_result(result))

    def test_duplicate_witnesses_and_minima_rejected(self):
        case = copy.deepcopy(self.saved["cases"][2])
        case["singleton_disagreement_witnesses"].append(
            copy.deepcopy(case["singleton_disagreement_witnesses"][0]))
        self.assertFalse(ac.verify_case_result(case))
        case = copy.deepcopy(self.saved["cases"][0])
        case["all_minimum_distinguishing_sets"].append(
            copy.deepcopy(case["all_minimum_distinguishing_sets"][0]))
        self.assertFalse(ac.verify_case_result(case))

    def test_cap_is_strict_and_sufficient_not_fixed_to_default(self):
        result = copy.deepcopy(self.saved)
        result["max_descriptions"] = 90000
        self.assertTrue(ac.verify_result(result))  # all exact counts fit
        for cap in (89437, 0, -1, 100001, True, 100000.0):
            result = copy.deepcopy(self.saved); result["max_descriptions"] = cap
            self.assertFalse(ac.verify_result(result))

    def test_public_solver_helpers_enforce_finite_integer_inputs(self):
        for n in (True, 2.0, 0, 4):
            with self.assertRaises(ValueError): ac.validate_assignment_set([0], n)
            with self.assertRaises(ValueError): ac.exact_minimum_distinguishing_set([0], 1, n)
        for mask in (-1, 16, True, 1.0):
            with self.assertRaises(ValueError): ac.disagreement_set(mask, 0, 2)
            with self.assertRaises(ValueError): ac.exact_minimum_distinguishing_set([], mask, 2)
        # A malformed tail must be rejected even when an earlier table is not hit.
        with self.assertRaises(ValueError): ac.is_distinguishing([], [0, -1], 1, 2)

if __name__=="__main__": unittest.main()
