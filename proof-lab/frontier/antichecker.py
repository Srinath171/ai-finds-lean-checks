"""Exact finite antichecker experiment.

Conjecture tested (for each stated ``(n, s)`` only):
  Let ``T`` be the lexicographically first truth table (assignment
  0 first: strings ``b0 b1 ...``) not realised by any NAND circuit of
  size <= ``s``.  Then there is a distinguishing assignment set ``A``
  with ``|A| <= s`` such that every realised truth table ``g`` differs
  from ``T`` on at least one assignment in ``A``.

Method: complete bounded enumeration reusing ``diagonal_lab``
(exact description count checked before enumeration, cap 100000),
then brute force over *all* subsets of the ``2**n <= 8`` assignment
points in increasing size for the EXACT minimum hitting set.
``A`` hits, for each realised ``g``, the disagreement set
``{j : g(j) != T(j)}``.

Finite scope only: a ``4 > 3`` outcome at ``(3, 3)`` does not prove
any ``omega(s)`` asymptotic, and nothing here is about P vs NP.
"""
from __future__ import annotations

import argparse
import importlib.util
import itertools
import json
import sys
from pathlib import Path

_HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("diagonal_lab", _HERE / "diagonal_lab.py")
dl = importlib.util.module_from_spec(_spec)
sys.modules.setdefault("diagonal_lab", dl)
_spec.loader.exec_module(dl)

CASES = ((2, 2), (2, 4), (3, 3))
MAX_DESCRIPTIONS = dl.DEFAULT_MAX_DESCRIPTIONS  # 100000
FORMAT = "antichecker-v1"
LEX_ORDER = "assignment 0 first: compare (b0, b1, ..., b_{2^n - 1})"
CONJECTURE = (
    "For lex-first missing T at (n,s), some distinguishing assignment "
    "set A with |A| <= s hits every realised truth table."
)
SCOPE_NOTE = (
    "Exact finite results for (2,2), (2,4), (3,3) only. "
    "A finite 4>3 outcome does not prove an omega(s) asymptotic lower bound, "
    "and nothing here proves or implies anything about P vs NP."
)


def _is_int(x) -> bool:
    return type(x) is int


def _same_json_value(actual, expected) -> bool:
    """Compare finite JSON-shaped data without bool/int/float aliases."""
    if type(actual) is not type(expected):
        return False
    if type(expected) is dict:
        return (actual.keys() == expected.keys()
                and all(_same_json_value(actual[k], v)
                        for k, v in expected.items()))
    if type(expected) is list:
        return (len(actual) == len(expected)
                and all(_same_json_value(a, b) for a, b in zip(actual, expected)))
    return actual == expected


def _model() -> dict:
    # Fresh values keep callers from mutating the verifier's expected metadata.
    return {"gate": "NAND (fan-in 2, ordered pairs, repetition allowed)",
            "assumptions": list(dl.MODEL_ASSUMPTIONS)}


def reachable_masks(n: int, s: int, max_descriptions: int = MAX_DESCRIPTIONS) -> list[int]:
    """Distinct masks realised by size<=s circuits, in lex (b0-first) order."""
    descs = dl.enumerate_descriptions(n, s, max_descriptions)  # cap pre-checked inside
    return sorted({dl.evaluate_mask(n, d) for d in descs}, key=lambda m: dl.lex_rank(m, n))


def lex_first_missing(n: int, reachable) -> int:
    """Lex-first (b0 b1 ...) missing mask; reachable is a collection of masks."""
    m = dl.first_missing_mask(reachable, n)
    if m is None:
        raise ValueError("no missing truth table")
    return m


def disagreement_set(g: int, target: int, n: int) -> tuple[int, ...]:
    dl._validate_n_s(n, 0)
    if (not _is_int(g) or not _is_int(target)
            or not 0 <= g < dl.num_functions(n)
            or not 0 <= target < dl.num_functions(n)):
        raise ValueError("masks must be in-range strict ints")
    return tuple(j for j in range(1 << n) if ((g >> j) & 1) != ((target >> j) & 1))


def validate_assignment_set(A, n: int) -> tuple[int, ...]:
    """Strict validation; raises ValueError on any malformed test set."""
    dl._validate_n_s(n, 0)
    if isinstance(A, (str, bytes)) or not isinstance(A, (list, tuple)):
        raise ValueError("assignment set must be a list/tuple of ints")
    seen = set()
    for j in A:
        if not _is_int(j):
            raise ValueError("assignment must be a strict int (no bool/float)")
        if not 0 <= j < (1 << n):
            raise ValueError("assignment out of range")
        if j in seen:
            raise ValueError("duplicate assignment")
        seen.add(j)
    return tuple(sorted(seen))


def is_distinguishing(A, reachable, target: int, n: int) -> bool:
    """True iff validated A hits every disagreement set. Raises on malformed A."""
    a = validate_assignment_set(A, n)
    dl._validate_target(n, target)
    aset = set(a)
    diffs = [disagreement_set(g, target, n) for g in reachable]
    return all(any(j in aset for j in d) for d in diffs)


def exact_minimum_distinguishing_set(reachable, target: int, n: int):
    """Brute all subsets of the 2**n points, increasing size. (min_size, lex-first min tuple, all mins)."""
    dl._validate_n_s(n, 0)
    dl._validate_target(n, target)
    points = range(1 << n)
    diffs = [set(disagreement_set(g, target, n)) for g in reachable]
    all_mins = []
    for r in range((1 << n) + 1):
        for A in itertools.combinations(points, r):
            aset = set(A)
            if all(aset & d for d in diffs):
                all_mins.append(A)
        if all_mins:
            return r, all_mins[0], all_mins
    raise ValueError("no distinguishing set (target itself reachable?)")


def run_case(n: int, s: int, max_descriptions: int = MAX_DESCRIPTIONS) -> dict:
    if not _is_int(n) or not _is_int(s) or (n, s) not in CASES:
        raise ValueError("only cases (2,2), (2,4), (3,3) are in scope")
    if not _is_int(max_descriptions) or not 1 <= max_descriptions <= MAX_DESCRIPTIONS:
        raise ValueError("max_descriptions must be an int in [1, 100000]")
    count = dl.description_count(n, s)
    if count > max_descriptions:
        raise ValueError("description count exceeds cap; refused before enumeration")
    reachable = reachable_masks(n, s, max_descriptions)
    target = lex_first_missing(n, reachable)
    min_size, best, all_mins = exact_minimum_distinguishing_set(reachable, target, n)
    # Four forcing witnesses for (3,3), derived (not assumed): singleton diffs.
    singletons = [
        {"reachable_mask": g, "forced_assignment": disagreement_set(g, target, n)[0]}
        for g in reachable if len(disagreement_set(g, target, n)) == 1
    ]
    return {
        "n": n, "s": s,
        "description_count_exact": count,
        "num_distinct_reachable": len(reachable),
        "reachable_masks_lex_order": reachable,
        "target_mask": target,
        "target_truth_vector": dl.truth_vector(target, n),
        "lex_order": LEX_ORDER,
        "minimum_distinguishing_size": min_size,
        "minimum_distinguishing_set": list(best),
        "all_minimum_distinguishing_sets": [list(a) for a in all_mins],
        "conjecture_holds_for_case": min_size <= s,
        "singleton_disagreement_witnesses": singletons,
    }


def run_experiment(max_descriptions: int = MAX_DESCRIPTIONS) -> dict:
    cases = [run_case(n, s, max_descriptions) for (n, s) in CASES]
    return {
        "format": FORMAT,
        "model": _model(),
        "max_descriptions": max_descriptions,
        "scope": SCOPE_NOTE,
        "conjecture": CONJECTURE,
        "cases": cases,
        "conjecture_holds_for_all_cases": all(c["conjecture_holds_for_case"] for c in cases),
        "counterexample_case": next(
            ({"n": c["n"], "s": c["s"], "target_mask": c["target_mask"],
              "minimum_distinguishing_size": c["minimum_distinguishing_size"],
              "minimum_distinguishing_set": c["minimum_distinguishing_set"]}
             for c in cases if not c["conjecture_holds_for_case"]), None),
    }


# ---------------------------------------------------------------------------
# Independent checker: Boolean simulation only (no mask arithmetic for eval),
# complete re-enumeration, exact coverage and exact minimality re-derived.
# ---------------------------------------------------------------------------

def _bool_mask(n, gates, output) -> int:
    mask = 0
    for a in range(1 << n):
        if dl.evaluate_bool(n, gates, output, a):
            mask |= 1 << a
    return mask


def verify_case_result(case) -> bool:
    """Strictly verify one case dict. False on partial/malformed/wrong data."""
    try:
        if not isinstance(case, dict):
            return False
        keys = {"n", "s", "description_count_exact", "num_distinct_reachable",
                "reachable_masks_lex_order", "target_mask", "target_truth_vector",
                "lex_order", "minimum_distinguishing_size",
                "minimum_distinguishing_set", "all_minimum_distinguishing_sets",
                "conjecture_holds_for_case", "singleton_disagreement_witnesses"}
        if set(case.keys()) != keys:
            return False
        n, s = case["n"], case["s"]
        if not _is_int(n) or not _is_int(s) or (n, s) not in CASES:
            return False
        # Complete independent re-enumeration via Boolean simulation.
        descs = dl.enumerate_descriptions(n, s, MAX_DESCRIPTIONS)
        if (not _is_int(case["description_count_exact"])
                or case["description_count_exact"] != dl.description_count(n, s)):
            return False
        if case["description_count_exact"] != len(descs):
            return False
        reachable_bool = sorted({_bool_mask(n, d.gates, d.output) for d in descs},
                                key=lambda m: dl.lex_rank(m, n))
        # Partial coverage is rejected: supplied list must be exactly complete.
        if not _same_json_value(case["reachable_masks_lex_order"], reachable_bool):
            return False
        if (not _is_int(case["num_distinct_reachable"])
                or case["num_distinct_reachable"] != len(reachable_bool)):
            return False
        target = case["target_mask"]
        if not _is_int(target) or target != dl.first_missing_mask(reachable_bool, n):
            return False
        if not _same_json_value(case["target_truth_vector"], dl.truth_vector(target, n)):
            return False
        if not _same_json_value(case["lex_order"], LEX_ORDER):
            return False
        # Lex-first: every lex-smaller table must be reachable (checked explicitly).
        for m in range(1 << (1 << n)):
            if dl.lex_rank(m, n) < dl.lex_rank(target, n) and m not in set(reachable_bool):
                return False
        A = validate_assignment_set(case["minimum_distinguishing_set"], n)
        if list(A) != case["minimum_distinguishing_set"]:
            return False  # must be stored sorted/unique
        if not _is_int(case["minimum_distinguishing_size"]):
            return False
        if case["minimum_distinguishing_size"] != len(A):
            return False
        if not is_distinguishing(A, reachable_bool, target, n):
            return False
        # Exact minimality re-derived by brute force over all subsets.
        min_size, best, all_mins = exact_minimum_distinguishing_set(reachable_bool, target, n)
        if min_size != case["minimum_distinguishing_size"] or list(best) != list(A):
            return False
        if not _same_json_value(case["all_minimum_distinguishing_sets"],
                                [list(a) for a in all_mins]):
            return False
        if case["conjecture_holds_for_case"] != (min_size <= s):
            return False
        if type(case["conjecture_holds_for_case"]) is not bool:
            return False
        singletons = [
            {"reachable_mask": g, "forced_assignment": disagreement_set(g, target, n)[0]}
            for g in reachable_bool if len(disagreement_set(g, target, n)) == 1
        ]
        if not _same_json_value(case["singleton_disagreement_witnesses"], singletons):
            return False
        return True
    except Exception:
        return False


def verify_result(result) -> bool:
    try:
        keys = {"format", "model", "max_descriptions", "scope", "conjecture",
                "cases", "conjecture_holds_for_all_cases", "counterexample_case"}
        if not isinstance(result, dict) or set(result) != keys:
            return False
        if (not _same_json_value(result["format"], FORMAT)
                or not _same_json_value(result["model"], _model())
                or not _same_json_value(result["scope"], SCOPE_NOTE)
                or not _same_json_value(result["conjecture"], CONJECTURE)):
            return False
        cap = result["max_descriptions"]
        if (not _is_int(cap) or not 1 <= cap <= MAX_DESCRIPTIONS
                or any(dl.description_count(n, s) > cap for n, s in CASES)):
            return False
        cases = result.get("cases")
        if not isinstance(cases, list) or len(cases) != len(CASES):
            return False
        if [(c.get("n"), c.get("s")) for c in cases] != list(CASES):
            return False
        if not all(verify_case_result(c) for c in cases):
            return False
        expected_ce = next(
            ({"n": c["n"], "s": c["s"], "target_mask": c["target_mask"],
              "minimum_distinguishing_size": c["minimum_distinguishing_size"],
              "minimum_distinguishing_set": c["minimum_distinguishing_set"]}
             for c in cases if not c["conjecture_holds_for_case"]), None)
        if not _same_json_value(result["counterexample_case"], expected_ce):
            return False
        if not _same_json_value(result["conjecture_holds_for_all_cases"], all(
                c["conjecture_holds_for_case"] for c in cases)):
            return False
        return True
    except Exception:
        return False


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description="Exact finite antichecker experiment")
    p.add_argument("--output", default=None)
    args = p.parse_args(argv)
    result = run_experiment()
    text = json.dumps(result, indent=2)
    if args.output:
        Path(args.output).write_text(text + "\n", encoding="utf-8")
    print(text)
    print("independent checker:", verify_result(result), file=sys.stderr)
    return 0 if verify_result(result) else 1


if __name__ == "__main__":
    raise SystemExit(main())
