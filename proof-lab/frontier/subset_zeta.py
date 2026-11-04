"""Exact bounded subset-zeta and positive-AND/symmetric truth-table evaluation.

This reconstructs one known evaluation kernel. It is not a subexhaustive SAT
algorithm, a Python-to-Lean refinement proof, or a P-versus-NP result.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
import hashlib
import json
from pathlib import Path
import random


MAX_N = 18
MAX_INPUT_BITS = 128
MAX_GATES = 4096
MAX_TABLE_ENTRIES = 1 << MAX_N
RESULT_PATH = Path(__file__).resolve().parent / "results" / "subset-zeta-demo.json"
HASH_NORMALIZATION = "CRLF->LF, then CR->LF; all other source bytes unchanged"
VECTOR_HASH_ENCODING = "UTF-8 compact JSON, ensure_ascii=True, no trailing newline"
SCOPE = (
    "Exact bounded truth-table evaluation of positive AND gates under an explicit "
    "symmetric top gate. O(n*2^n) table work does not achieve a 2^n/n^k SAT "
    "saving; no full Williams implication, Python/Lean refinement, novelty, or "
    "P-versus-NP claim."
)


class Refusal(Exception):
    """A malformed or over-cap request has no SAT verdict."""

    def __init__(self, status, reason):
        super().__init__(reason)
        self.status = status


@dataclass
class Counters:
    validation_checks: int = 0
    scalar_additions: int = 0
    histogram_additions: int = 0
    support_mask_or_operations: int = 0
    top_membership_checks: int = 0
    max_integer_bits: int = 0

    def record(self, value):
        # Tracks histogram/value arithmetic, excluding indices and counters.
        self.max_integer_bits = max(self.max_integer_bits, value.bit_length())

    def report(self):
        return {
            **asdict(self),
            "total_scalar_additions": self.scalar_additions + self.histogram_additions,
        }


def _require(condition, reason, counters, *, resource=False):
    counters.validation_checks += 1
    if not condition:
        raise Refusal("RESOURCE_LIMIT" if resource else "MALFORMED", reason)


def _validate_n(n, counters):
    _require(type(n) is int, "n_must_be_exact_int", counters)
    _require(n >= 0, "n_must_be_nonnegative", counters)
    _require(n <= MAX_N, "n_limit", counters, resource=True)


def _failure(exc, n, counters):
    return {
        "status": exc.status,
        "reason": str(exc),
        "n": n if type(n) is int else None,
        "zeta": None,
        "gate_counts": None,
        "truth_table": None,
        "satisfiable": None,
        "counters": counters.report(),
    }


def _zeta_recursive(table, counters):
    """Highest-bit split; numeric indices use little-endian variable masks."""
    if len(table) == 1:
        return [table[0]]
    half = len(table) // 2
    left = _zeta_recursive(table[:half], counters)
    right = _zeta_recursive(table[half:], counters)
    upper = []
    for lower_value, upper_value in zip(left, right):
        value = lower_value + upper_value
        counters.scalar_additions += 1
        counters.record(value)
        upper.append(value)
    return left + upper


def subset_zeta(n, histogram):
    """Return g[A] = sum(histogram[S] for S subset of A), with exact counters.

    Inputs must be a list/tuple of 2**n nonnegative exact integers of at most
    128 bits, with 0 <= n <= 18. Booleans and integer subclasses are refused.
    No override can increase these fixed caps. Refusals return no SAT verdict.
    """
    counters = Counters()
    try:
        _validate_n(n, counters)
        _require(type(histogram) in (list, tuple), "histogram_must_be_list_or_tuple", counters)
        _require(len(histogram) <= MAX_TABLE_ENTRIES, "table_entry_limit", counters, resource=True)
        _require(len(histogram) == 1 << n, "histogram_length_mismatch", counters)
        for value in histogram:
            _require(type(value) is int, "histogram_value_must_be_exact_int", counters)
            _require(value >= 0, "histogram_value_must_be_nonnegative", counters)
            _require(value.bit_length() <= MAX_INPUT_BITS, "histogram_value_bit_limit", counters, resource=True)
            counters.record(value)
        transformed = _zeta_recursive(list(histogram), counters)
    except Refusal as exc:
        return _failure(exc, n, counters)
    return {
        "status": "TRANSFORMED",
        "n": n,
        "zeta": transformed,
        "expected_scalar_additions": n * (1 << (n - 1)) if n else 0,
        "output_bit_bound": MAX_INPUT_BITS + n,
        "counters": counters.report(),
    }


def evaluate_positive_and_sym(n, supports, accept_counts):
    """Evaluate every assignment of one bounded positive-AND/SYM circuit.

    supports is a list/tuple of at most 4096 list/tuple supports, each of length
    <= n, with variable indices 0..n-1. Repeated literals are allowed and mean
    the same AND; repeated gates retain multiplicity. An empty AND is true.
    accept_counts is an explicit list of accepted numbers of satisfied gates,
    containing only exact integers 0..len(supports), at most len(supports)+1
    entries (hence at most 4097).
    Duplicate accepted counts are harmless. No executable top-gate callback is
    accepted. Numeric mask bit i is variable i; true output is Boolean True.
    """
    counters = Counters()
    try:
        _validate_n(n, counters)
        _require(type(supports) in (list, tuple), "supports_must_be_list_or_tuple", counters)
        _require(len(supports) <= MAX_GATES, "gate_count_limit", counters, resource=True)
        masks = []
        for support in supports:
            _require(type(support) in (list, tuple), "support_must_be_list_or_tuple", counters)
            _require(len(support) <= n, "support_length_limit", counters, resource=True)
            mask = 0
            for variable in support:
                _require(type(variable) is int, "variable_must_be_exact_int", counters)
                _require(0 <= variable < n, "variable_index_out_of_range", counters)
                mask |= 1 << variable
                counters.support_mask_or_operations += 1
            masks.append(mask)
        _require(type(accept_counts) is list, "accept_counts_must_be_list", counters)
        _require(len(accept_counts) <= len(supports) + 1, "accept_count_entry_limit", counters, resource=True)
        for count in accept_counts:
            _require(type(count) is int, "accepted_count_must_be_exact_int", counters)
            _require(0 <= count <= len(supports), "accepted_count_out_of_range", counters)
        accepted = [False] * (len(supports) + 1)
        for count in accept_counts:
            accepted[count] = True
        histogram = [0] * (1 << n)
        for mask in masks:
            histogram[mask] += 1
            counters.histogram_additions += 1
            counters.record(histogram[mask])
        gate_counts = _zeta_recursive(histogram, counters)
        truth_table = []
        for count in gate_counts:
            truth_table.append(accepted[count])
            counters.top_membership_checks += 1
    except Refusal as exc:
        return _failure(exc, n, counters)
    return {
        "status": "EVALUATED",
        "n": n,
        "gates": len(supports),
        "histogram": histogram,
        "gate_counts": gate_counts,
        "truth_table": truth_table,
        "satisfiable": any(truth_table),
        "satisfying_assignments": sum(truth_table),
        "expected_scalar_additions": n * (1 << (n - 1)) if n else 0,
        "counters": counters.report(),
    }


def _vector_hash(vector):
    payload = json.dumps(vector, ensure_ascii=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def source_hash_lf():
    data = Path(__file__).read_bytes().replace(b"\r\n", b"\n").replace(b"\r", b"\n")
    return hashlib.sha256(data).hexdigest()


def make_demo_inputs(n=16, gates=1024, seed=20261104):
    """A reproducible bounded input; this is not a hard-instance distribution."""
    counters = Counters()
    _validate_n(n, counters)
    _require(type(gates) is int, "gates_must_be_exact_int", counters)
    _require(0 <= gates <= MAX_GATES, "gate_count_limit", counters, resource=True)
    _require(type(seed) is int, "seed_must_be_exact_int", counters)
    rng = random.Random(seed)
    supports = [
        [rng.randrange(n) for _ in range(rng.randrange(min(n, 8) + 1))]
        if n else []
        for _ in range(gates)
    ]
    accept_counts = [count for count in range(gates + 1) if count % 7 in (2, 5)]
    return supports, accept_counts


def experiment(n=16, gates=1024, seed=20261104):
    supports, accept_counts = make_demo_inputs(n, gates, seed)
    result = evaluate_positive_and_sym(n, supports, accept_counts)
    if result["status"] != "EVALUATED":
        raise RuntimeError("internally generated demo was refused")
    size = 1 << n
    rng = random.Random(seed + 1)
    sample_masks = sorted({0, size - 1, size // 2, *[rng.randrange(size) for _ in range(21)]})
    samples = []
    for mask in sample_masks:
        # Independent source-expression evaluation, without histogram masks.
        direct_count = sum(all((mask >> variable) & 1 for variable in support) for support in supports)
        direct_value = direct_count in accept_counts
        if (direct_count != result["gate_counts"][mask]
                or direct_value != result["truth_table"][mask]):
            raise AssertionError("independent demo sample mismatch")
        samples.append({"mask": mask, "gate_count": direct_count, "value": direct_value})
    return {
        "format": "subset-zeta-demo-v1",
        "status": result["status"],
        "scope": SCOPE,
        "source_sha256_lf": source_hash_lf(),
        "source_hash_normalization": HASH_NORMALIZATION,
        "vector_hash_encoding": VECTOR_HASH_ENCODING,
        "limits": {"max_n": MAX_N, "max_input_bits": MAX_INPUT_BITS, "max_gates": MAX_GATES},
        "input": {
            "n": n, "gates": gates, "seed": seed,
            "generator": "Python random.Random; widths uniform 0..min(n,8), literals sampled with replacement",
            "top_rule": "accept iff number of true bottom gates modulo 7 is 2 or 5",
            "support_lists_sha256": _vector_hash(supports),
            "accept_counts_sha256": _vector_hash(accept_counts),
            "accepted_count_entries": len(accept_counts),
            "support_literal_entries": sum(map(len, supports)),
            "empty_and_gates": sum(not support for support in supports),
            "first_supports": supports[:8],
        },
        "table_entries": size,
        "histogram_sha256": _vector_hash(result["histogram"]),
        "gate_counts_sha256": _vector_hash(result["gate_counts"]),
        "truth_table_sha256": _vector_hash(result["truth_table"]),
        "satisfiable": result["satisfiable"],
        "satisfying_assignments": result["satisfying_assignments"],
        "minimum_true_gate_count": min(result["gate_counts"]),
        "maximum_true_gate_count": max(result["gate_counts"]),
        "expected_scalar_additions": result["expected_scalar_additions"],
        "counters": result["counters"],
        "independent_sample_rows_checked": len(samples),
        "samples": samples,
        "verification_scope": "All table entries computed; independent source-expression oracle checked only these sampled rows. Unit tests separately compare entire bounded tables.",
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-demo", action="store_true", help="write the fixed project results path")
    args = parser.parse_args(argv)
    report = experiment()
    text = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.write_demo:
        RESULT_PATH.write_text(text, encoding="utf-8", newline="\n")
    print(text, end="")


if __name__ == "__main__":
    main()
