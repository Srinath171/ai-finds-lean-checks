"""Bounded exact finite experiment: explicit diagonal hard truth tables.

Scope
-----
For fixed small ``n`` (1..3) and ``s`` (0..4) this module enumerates *every*
topological NAND circuit description of size at most ``s``, evaluates each
one, and picks the lexicographically first truth table (see below) that no
enumerated description computes.  It then builds an independently checkable
certificate: one disagreement assignment for every enumerated description.
The certificate checkers establish only that the target is not computed at
size <= s. They do not certify that it is lexicographically first missing
or maximally hard; selecting the first missing table is a separate search.

This is an exact statement about the stated finite ``(n, s)`` only.  It is
not a P-versus-NP solution, it proves no asymptotic lower bound, and the
length of the long certificate built here does not exclude the existence
of some other, shorter certificate.  See ``DIAGONAL_EXPERIMENT.md``.

Model (identical conventions to ``circuit_lab.py`` / ``CircuitCounting.lean``)
------------------------------------------------------------------------------
* Inputs are ``x0 .. x(n-1)`` only.  No free constants and no free
  complemented inputs.
* The only gate is binary NAND.  Fan-in is exactly two, ordered pairs are
  distinct descriptions, and repetition is allowed (``NAND(v, v) = NOT v``).
* Fanout is unlimited (DAG sharing).  The output may be any input or any
  gate output.  Size is the number of NAND gates.
* Signals are indexed ``0..n-1`` for inputs and ``n+i`` for gate ``i``
  (0-based).  Gate ``i`` chooses both fan-ins from the ``n+i`` earlier
  signals.  A description of size ``k`` is a gate list of length ``k``
  plus one output index in ``[0, n+k)``.
* Assignments ``a`` range over ``[0, 2**n)``; bit ``i`` of ``a`` is the
  value of ``xi``.  A truth-table mask has bit ``a`` set iff the function
  is 1 on assignment ``a`` (for ``n=2``: x0=10, x1=12, XOR=6).

Lexicographic order and the mex rule
------------------------------------
A truth table is read as the string ``b0 b1 ... b_{2**n - 1}`` (assignment
0 first).  "Lexicographically first missing" compares those strings, i.e.
it compares ``(b0, b1, ...)`` tuples.  The rank of a mask in this order is
its bit-reversal ``lex_rank``.  The first missing table is found by taking
the mex (smallest non-negative integer not present) of the sorted lex
ranks of the *distinct computed* masks.  At most ``distinct + 1`` ranks are
ever inspected, so the search never scans the ``2**(2**n)``-sized truth
table universe.  The universe size, the description count, and the
distinct-function count are three different numbers and are reported
separately.

Caps
----
The exact description count
``sum_{k<=s} (n+k) * prod_{i<k} (n+i)**2`` is computed *before* any
enumeration.  If it exceeds ``max_descriptions`` (default 100000) the
lower-level enumeration raises :class:`DescriptionCapExceeded` without
enumerating anything, and :func:`run_experiment` returns status
``"REFUSED"`` with the missing table reported as ``"UNKNOWN"``.
"""

from __future__ import annotations

import argparse
import json
import sys
from typing import NamedTuple

MAX_N = 3
MAX_S = 4
DEFAULT_MAX_DESCRIPTIONS = 100_000
UNKNOWN = "UNKNOWN"
REFUSED = "REFUSED"

MODEL_ASSUMPTIONS = [
    "inputs are the variables x0..x(n-1) only",
    "no free constants: 0 and 1 are not available unless built by gates",
    "no free complemented inputs: NOT xi is not available unless built",
    "only gate is binary NAND; fan-in exactly two; ordered pairs; repetition allowed (NAND(v,v) = NOT v)",
    "unlimited fanout: computed signals may be reused by any later gates (DAG sharing)",
    "output may be any input or computed signal; size = number of NAND gates",
    "truth tables are bit masks over assignments a in [0, 2**n), bit i of a = value of xi",
]

SCOPE_NOTE = (
    "Exact finite result for the stated (n, s) and caps only. "
    "No all-n, asymptotic, superpolynomial, or P-vs-NP claim is made or implied. "
    "A long explicit certificate here does not rule out a different short certificate."
)

CERT_FORMAT = "diagonal-certificate-v1"
EXPERIMENT_FORMAT = "diagonal-experiment-v1"


class DescriptionCapExceeded(ValueError):
    """Exact description count exceeds the cap; raised before enumeration."""

    def __init__(self, n: int, s: int, count: int, max_descriptions: int):
        super().__init__(
            "description count %d for n=%d, s=%d exceeds max_descriptions=%d; "
            "refused before enumeration" % (count, n, s, max_descriptions)
        )
        self.n = n
        self.s = s
        self.count = count
        self.max_descriptions = max_descriptions


# Backwards-friendly alias.
CapExceededError = DescriptionCapExceeded


# ---------------------------------------------------------------------------
# Validation helpers (strict: bool is not an int anywhere in this module)
# ---------------------------------------------------------------------------

def _is_int(x) -> bool:
    return type(x) is int


def _validate_n_s(n, s) -> tuple[int, int]:
    if not _is_int(n) or not 1 <= n <= MAX_N:
        raise ValueError("n must be an integer with 1 <= n <= %d" % MAX_N)
    if not _is_int(s) or not 0 <= s <= MAX_S:
        raise ValueError("s must be an integer with 0 <= s <= %d" % MAX_S)
    return n, s


def _validate_max_descriptions(max_descriptions) -> int:
    if not _is_int(max_descriptions) or max_descriptions < 1:
        raise ValueError("max_descriptions must be a positive integer")
    return max_descriptions


def _validate_target(n: int, target_mask) -> int:
    if not _is_int(target_mask) or not 0 <= target_mask < (1 << (1 << n)):
        raise ValueError("target_mask out of range for n=%d" % n)
    return target_mask


# ---------------------------------------------------------------------------
# Truth tables (mask arithmetic; checker below uses Boolean simulation)
# ---------------------------------------------------------------------------

def num_assignments(n: int) -> int:
    return 1 << n


def truth_table_bits(n: int) -> int:
    """Number of output bits in one n-input truth table: 2**n."""
    return 1 << n


def num_functions(n: int) -> int:
    """Size of the truth-table universe: 2**(2**n). Not enumerated."""
    return 1 << (1 << n)


def full_mask(n: int) -> int:
    return (1 << (1 << n)) - 1


def input_masks(n: int) -> tuple[int, ...]:
    _validate_n_s(n, 0)
    return tuple(
        sum(1 << a for a in range(1 << n) if (a >> i) & 1) for i in range(n)
    )


def nand_mask(a: int, b: int, n: int) -> int:
    return full_mask(n) ^ (a & b)


def truth_vector(mask: int, n: int) -> list[int]:
    """Output bits in assignment order a = 0, 1, ..., 2**n - 1."""
    return [(mask >> a) & 1 for a in range(1 << n)]


# ---------------------------------------------------------------------------
# Exact description counting (matches descCountUpTo in CircuitCounting.lean)
# ---------------------------------------------------------------------------

def prod_count(n: int, k: int) -> int:
    """prod_{i<k} (n+i)**2; the empty product (k=0) is 1."""
    if not _is_int(n) or n < 1:
        raise ValueError("n must be a positive integer")
    if not _is_int(k) or k < 0:
        raise ValueError("k must be a nonnegative integer")
    result = 1
    for i in range(k):
        result *= (n + i) ** 2
    return result


def descriptions_of_size_count(n: int, k: int) -> int:
    """Exact number of size-exactly-k descriptions: (n+k) * prodCount n k."""
    if not _is_int(k) or k < 0:
        raise ValueError("k must be a nonnegative integer")
    return (n + k) * prod_count(n, k)


def description_count(n: int, s: int) -> int:
    """Exact number of descriptions of size at most s (no enumeration)."""
    _validate_n_s(n, s)
    return sum(descriptions_of_size_count(n, k) for k in range(s + 1))


# Aliases.
exact_description_count = description_count
count_descriptions = description_count
desc_count_up_to = description_count


# ---------------------------------------------------------------------------
# Descriptions and deterministic enumeration
# ---------------------------------------------------------------------------

class Description(NamedTuple):
    """One circuit description: a topological NAND gate list + output."""

    gates: tuple
    output: int

    @property
    def size(self) -> int:
        return len(self.gates)

    def to_dict(self) -> dict:
        return {"gates": [[i, j] for (i, j) in self.gates], "output": self.output}


# Alias matching circuit terminology.
CircuitDescription = Description


def _gate_sequences(n: int, k: int) -> list[tuple[tuple[int, int], ...]]:
    """All gate lists of length k, in deterministic generation order.

    Sequences are built gate by gate; at step ``i`` the ordered fan-in
    pairs are ``[(a, b) for a in range(n+i) for b in range(n+i)]`` in that
    order, appended to every prefix in order.  The enumeration ID of a
    description is its index in :func:`enumerate_descriptions` output.
    """
    seqs: list[tuple[tuple[int, int], ...]] = [()]
    for i in range(k):
        pairs = [(a, b) for a in range(n + i) for b in range(n + i)]
        seqs = [seq + (p,) for seq in seqs for p in pairs]
    return seqs


def enumerate_descriptions(n: int, s: int,
                           max_descriptions: int = DEFAULT_MAX_DESCRIPTIONS
                           ) -> list[Description]:
    """Every description of size <= s, in deterministic ID order.

    The exact count is precomputed first; if it exceeds the cap,
    :class:`DescriptionCapExceeded` is raised before anything is built.
    Order: increasing size k, then gate-sequence generation order, then
    increasing output index.  IDs are ``0 .. count-1`` in this order.
    """
    _validate_n_s(n, s)
    _validate_max_descriptions(max_descriptions)
    count = description_count(n, s)
    if count > max_descriptions:
        raise DescriptionCapExceeded(n, s, count, max_descriptions)
    out: list[Description] = []
    for k in range(s + 1):
        for seq in _gate_sequences(n, k):
            for output in range(n + k):
                out.append(Description(gates=seq, output=output))
    if len(out) != count:  # internal invariant; exact-count cross-check
        raise RuntimeError("enumeration length != exact description count")
    return out


# Aliases.
enumerate_circuits = enumerate_descriptions
all_descriptions = enumerate_descriptions


def _parse_gates(n: int, gates_raw, size_hint=None):
    """Strictly parse a gate list; return tuple of pairs or None."""
    if not isinstance(gates_raw, (list, tuple)):
        return None
    gates = []
    for k, gate in enumerate(gates_raw):
        if not isinstance(gate, (list, tuple)) or len(gate) != 2:
            return None
        i, j = gate
        if not _is_int(i) or not _is_int(j):
            return None
        if not (0 <= i < n + k and 0 <= j < n + k):
            return None
        gates.append((i, j))
    if size_hint is not None and len(gates) != size_hint:
        return None
    return tuple(gates)


def _parse_description(n: int, d):
    """Strictly parse {'gates': ..., 'output': ...}; Description or None."""
    if not isinstance(d, dict) or set(d.keys()) != {"gates", "output"}:
        return None
    gates = _parse_gates(n, d["gates"])
    if gates is None or not _is_int(d["output"]):
        return None
    if not 0 <= d["output"] < n + len(gates):
        return None
    return Description(gates=gates, output=d["output"])


# ---------------------------------------------------------------------------
# Evaluation: mask arithmetic (search) and Boolean simulation (checker)
# ---------------------------------------------------------------------------

def evaluate_mask(n: int, description: Description) -> int:
    """Truth-table mask of a description, by mask arithmetic."""
    signals = list(input_masks(n))
    full = full_mask(n)
    for (i, j) in description.gates:
        signals.append(full ^ (signals[i] & signals[j]))
    return signals[description.output]


def evaluate_bool(n: int, gates, output: int, assignment: int) -> bool:
    """Boolean NAND simulation on one assignment. No mask arithmetic.

    ``assignment`` is an integer in ``[0, 2**n)``; bit i is xi's value.
    This is the only evaluation the certificate checkers rely on.
    """
    signals = [bool((assignment >> i) & 1) for i in range(n)]
    for (i, j) in gates:
        signals.append(not (signals[i] and signals[j]))
    return signals[output]


# Aliases.
circuit_mask = evaluate_mask
evaluate_circuit_mask = evaluate_mask
evaluate_on_assignment = evaluate_bool
eval_on_assignment = evaluate_bool


def computed_masks(descriptions, n: int) -> list[int]:
    """Mask computed by each description, in enumeration-ID order."""
    return [evaluate_mask(n, d) for d in descriptions]


# ---------------------------------------------------------------------------
# Lexicographic rank and mex (never scan the 2**(2**n) universe)
# ---------------------------------------------------------------------------

def lex_rank(mask: int, n: int) -> int:
    """Rank of a truth table in (b0, b1, ..., b_{2**n-1}) lex order.

    This is the bit-reversal of the mask within 2**n bits: b0 becomes the
    most significant rank bit.
    """
    m = 1 << n
    rank = 0
    for a in range(m):
        if (mask >> a) & 1:
            rank |= 1 << (m - 1 - a)
    return rank


def lex_unrank(rank: int, n: int) -> int:
    """Inverse of :func:`lex_rank`."""
    m = 1 << n
    mask = 0
    for a in range(m):
        if (rank >> (m - 1 - a)) & 1:
            mask |= 1 << a
    return mask


def mex(values) -> int:
    """Smallest non-negative integer not in ``values`` (any iterable)."""
    seen = set(values)
    r = 0
    while r in seen:
        r += 1
    return r


def mex_sorted(sorted_unique) -> int:
    """Mex of an already sorted, duplicate-free sequence, in one pass."""
    expected = 0
    for v in sorted_unique:
        if v == expected:
            expected += 1
        elif v > expected:
            break
    return expected


def first_missing_mask(computed, n: int):
    """Lexicographically first mask not in ``computed`` (iterable of masks).

    Uses the mex of the sorted lex ranks of the distinct computed masks,
    inspecting at most ``distinct + 1`` ranks.  Returns None when every
    one of the ``2**(2**n)`` functions is computed.
    """
    _validate_n_s(n, 0)
    ranks = sorted({lex_rank(m, n) for m in computed})
    r = mex_sorted(ranks)
    if r >= num_functions(n):
        return None
    return lex_unrank(r, n)


# Aliases.
find_missing_mask = first_missing_mask
lexicographically_first_missing = first_missing_mask
diagonal_hard_mask = first_missing_mask


def _smallest_disagreement(circuit_mask_value: int, target_mask: int, n: int) -> int:
    """Smallest assignment where two masks differ (they must differ)."""
    diff = circuit_mask_value ^ target_mask
    if diff == 0:
        raise ValueError("masks agree everywhere; no disagreement assignment")
    a = 0
    while not (diff >> a) & 1:
        a += 1
    return a


# ---------------------------------------------------------------------------
# Canonical bytes and metrics
# ---------------------------------------------------------------------------

def canonical_json_bytes(obj) -> bytes:
    """Deterministic JSON encoding used for all byte counts."""
    return json.dumps(obj, sort_keys=True, separators=(",", ":")).encode("utf-8")


def certificate_metrics(
        cert: dict, max_descriptions: int = DEFAULT_MAX_DESCRIPTIONS) -> dict:
    """Actual byte/row/operation counts for a certificate built here.

    Gate operations = NAND evaluations the checker performs while
    checking rows (naive: one single-assignment evaluation per row;
    grouped: one full truth table per covered description).
    Literal operations = fan-in signal reads = 2 per gate operation.
    """
    _validate_max_descriptions(max_descriptions)
    if not isinstance(cert, dict):
        raise ValueError("certificate must be an object")
    kind = cert.get("kind")
    n = cert.get("n")
    data = canonical_json_bytes(cert)
    if kind == "naive-per-circuit":
        rows = cert["rows"]
        gate_ops = sum(len(r["gates"]) for r in rows)
        return {
            "kind": kind,
            "certificate_bytes": len(data),
            "num_rows": len(rows),
            "num_descriptions": cert["num_descriptions"],
            "truth_table_bits": truth_table_bits(n),
            "checker_gate_operations": gate_ops,
            "checker_literal_operations": 2 * gate_ops,
        }
    if kind == "grouped-by-truth-table":
        descriptions = enumerate_descriptions(n, cert["s"], max_descriptions)
        covered = [i for g in cert["groups"] for i in g["description_ids"]]
        gate_ops = sum(
            len(descriptions[i].gates) * (1 << n) for i in covered
        )
        return {
            "kind": kind,
            "certificate_bytes": len(data),
            "num_rows": len(cert["groups"]),
            "num_descriptions": cert["num_descriptions"],
            "num_covered_ids": len(covered),
            "truth_table_bits": truth_table_bits(n),
            "checker_gate_operations": gate_ops,
            "checker_literal_operations": 2 * gate_ops,
        }
    raise ValueError("unknown certificate kind: %r" % (kind,))


# ---------------------------------------------------------------------------
# Naive per-circuit certificate: builder and strict checker
# ---------------------------------------------------------------------------

_NAIVE_TOP_KEYS = {
    "format", "kind", "n", "s", "target_mask", "target_truth_vector",
    "num_descriptions", "num_functions_universe", "truth_table_bits", "rows",
}
_NAIVE_ROW_KEYS = {
    "id", "gates", "output", "assignment", "circuit_output", "target_output",
}


def build_certificate(n: int, s: int, target_mask=None,
                      max_descriptions: int = DEFAULT_MAX_DESCRIPTIONS) -> dict:
    """Naive certificate: one disagreement row per enumerated description.

    If ``target_mask`` is omitted, the lexicographically first missing
    mask is used.  Raises ValueError if there is no missing mask or the
    given target is in fact computed by some size-<=s description.
    """
    _validate_n_s(n, s)
    descriptions = enumerate_descriptions(n, s, max_descriptions)
    masks = computed_masks(descriptions, n)
    distinct = set(masks)
    if target_mask is None:
        target_mask = first_missing_mask(distinct, n)
        if target_mask is None:
            raise ValueError("no missing truth table at n=%d, s=%d" % (n, s))
    _validate_target(n, target_mask)
    if target_mask in distinct:
        raise ValueError(
            "target_mask %d is computed by a size<=%d description; "
            "no disagreement assignment exists for that description"
            % (target_mask, s))
    rows = []
    for idx, (desc, cmask) in enumerate(zip(descriptions, masks)):
        a = _smallest_disagreement(cmask, target_mask, n)
        rows.append({
            "id": idx,
            "gates": [[i, j] for (i, j) in desc.gates],
            "output": desc.output,
            "assignment": a,
            # Filled by Boolean simulation, cross-checking the mask search.
            "circuit_output": int(evaluate_bool(n, desc.gates, desc.output, a)),
            "target_output": (target_mask >> a) & 1,
        })
    return {
        "format": CERT_FORMAT,
        "kind": "naive-per-circuit",
        "n": n,
        "s": s,
        "target_mask": target_mask,
        "target_truth_vector": truth_vector(target_mask, n),
        "num_descriptions": len(descriptions),
        "num_functions_universe": num_functions(n),
        "truth_table_bits": truth_table_bits(n),
        "rows": rows,
    }


# Aliases.
make_certificate = build_certificate
generate_certificate = build_certificate
build_naive_certificate = build_certificate


def _check_header(cert, kind: str, top_keys: set):
    """Shared strict header validation. Returns (n, s, target) or None."""
    if not isinstance(cert, dict) or set(cert.keys()) != top_keys:
        return None
    if cert.get("format") != CERT_FORMAT or cert.get("kind") != kind:
        return None
    n, s, target = cert.get("n"), cert.get("s"), cert.get("target_mask")
    if not _is_int(n) or not _is_int(s) or not _is_int(target):
        return None
    if not (1 <= n <= MAX_N and 0 <= s <= MAX_S):
        return None
    if not 0 <= target < num_functions(n):
        return None
    vector = cert.get("target_truth_vector")
    if (not isinstance(vector, list) or len(vector) != truth_table_bits(n)
            or any(not _is_int(bit) or bit not in (0, 1) for bit in vector)
            or vector != truth_vector(target, n)):
        return None
    if (not _is_int(cert.get("truth_table_bits"))
            or cert["truth_table_bits"] != truth_table_bits(n)):
        return None
    if kind == "naive-per-circuit":
        if (not _is_int(cert.get("num_functions_universe"))
                or cert["num_functions_universe"] != num_functions(n)):
            return None
    return n, s, target


def verify_certificate_detailed(cert,
                                max_descriptions: int = DEFAULT_MAX_DESCRIPTIONS
                                ) -> dict:
    """Strictly verify a naive certificate; report checker operation counts.

    Re-enumerates every description (after the same precomputed cap
    check), requires exactly one well-formed row per enumeration ID,
    and for each row re-evaluates the circuit by Boolean NAND simulation
    on the row's assignment.  Any missing, duplicate, extra, or malformed
    row, any wiring that differs from the enumerated description, and any
    assignment on which circuit and target agree makes it invalid.
    Validity establishes non-computability at size <= s only. It does not
    establish lexicographic minimality or maximum circuit complexity.
    """
    result = {"valid": False, "reason": None, "rows_checked": 0,
              "descriptions_expected": 0, "checker_gate_operations": 0,
              "checker_literal_operations": 0}

    def fail(reason):
        result["reason"] = reason
        return result

    try:
        _validate_max_descriptions(max_descriptions)
    except ValueError as exc:
        return fail(str(exc))
    header = _check_header(cert, "naive-per-circuit", _NAIVE_TOP_KEYS)
    if header is None:
        return fail("malformed certificate header")
    n, s, target = header
    count = description_count(n, s)
    if count > max_descriptions:
        return fail("description count %d exceeds cap %d; refused"
                    % (count, max_descriptions))
    if (not _is_int(cert.get("num_descriptions"))
            or cert["num_descriptions"] != count):
        return fail("num_descriptions does not match exact description count")
    descriptions = enumerate_descriptions(n, s, max_descriptions)
    result["descriptions_expected"] = count
    rows = cert.get("rows")
    if not isinstance(rows, list) or len(rows) != count:
        return fail("rows must be a list with exactly one row per description")
    seen: set[int] = set()
    gate_ops = 0
    for row in rows:
        if not isinstance(row, dict) or set(row.keys()) != _NAIVE_ROW_KEYS:
            return fail("malformed row")
        rid = row["id"]
        if not _is_int(rid) or not 0 <= rid < count:
            return fail("row id out of range")
        if rid in seen:
            return fail("duplicate row id %d" % rid)
        seen.add(rid)
        desc = descriptions[rid]
        gates = _parse_gates(n, row["gates"])
        if gates is None or gates != desc.gates:
            return fail("row %d gates do not match enumerated description" % rid)
        if not _is_int(row["output"]) or row["output"] != desc.output:
            return fail("row %d output does not match enumerated description" % rid)
        a = row["assignment"]
        if not _is_int(a) or not 0 <= a < (1 << n):
            return fail("row %d assignment out of range" % rid)
        if not _is_int(row["circuit_output"]) or row["circuit_output"] not in (0, 1):
            return fail("row %d circuit_output is not a bit" % rid)
        if not _is_int(row["target_output"]) or row["target_output"] not in (0, 1):
            return fail("row %d target_output is not a bit" % rid)
        # The actual check: Boolean NAND simulation on this assignment.
        circuit_bit = int(evaluate_bool(n, desc.gates, desc.output, a))
        gate_ops += len(desc.gates)
        if circuit_bit != row["circuit_output"]:
            return fail("row %d circuit_output does not match Boolean evaluation" % rid)
        if ((target >> a) & 1) != row["target_output"]:
            return fail("row %d target_output does not match target table" % rid)
        if circuit_bit == row["target_output"]:
            return fail("row %d assignment is not a disagreement" % rid)
        result["rows_checked"] += 1
    if seen != set(range(count)):
        return fail("row ids do not cover every enumerated description")
    result["checker_gate_operations"] = gate_ops
    result["checker_literal_operations"] = 2 * gate_ops
    result["valid"] = True
    return result


def verify_certificate(cert,
                       max_descriptions: int = DEFAULT_MAX_DESCRIPTIONS) -> bool:
    """True iff ``cert`` is a complete, correct naive certificate."""
    try:
        return verify_certificate_detailed(cert, max_descriptions)["valid"]
    except Exception:
        return False


# Aliases.
check_certificate = verify_certificate
validate_certificate = verify_certificate


# ---------------------------------------------------------------------------
# Grouped certificate (by equal computed truth table) and its checker
# ---------------------------------------------------------------------------

_GROUPED_TOP_KEYS = {
    "format", "kind", "n", "s", "target_mask", "target_truth_vector",
    "num_descriptions", "num_distinct_computed", "truth_table_bits", "groups",
}
_GROUP_KEYS = {
    "computed_mask", "assignment", "circuit_output", "target_output",
    "description_ids",
}


def build_grouped_certificate(n: int, s: int, target_mask=None,
                              max_descriptions: int = DEFAULT_MAX_DESCRIPTIONS
                              ) -> dict:
    """Group descriptions by computed truth table, with explicit coverage.

    One group per distinct computed mask, holding one disagreement
    assignment for that mask plus the explicit list of description IDs
    computing it.  The ID lists are the coverage proof: dropping them
    leaves a short list that by itself certifies nothing (see MD).
    """
    _validate_n_s(n, s)
    descriptions = enumerate_descriptions(n, s, max_descriptions)
    masks = computed_masks(descriptions, n)
    distinct = set(masks)
    if target_mask is None:
        target_mask = first_missing_mask(distinct, n)
        if target_mask is None:
            raise ValueError("no missing truth table at n=%d, s=%d" % (n, s))
    _validate_target(n, target_mask)
    if target_mask in distinct:
        raise ValueError("target_mask %d is computed at size<=%d" % (target_mask, s))
    by_mask: dict[int, list[int]] = {}
    for idx, cmask in enumerate(masks):
        by_mask.setdefault(cmask, []).append(idx)
    groups = []
    for cmask in sorted(by_mask, key=lambda m: lex_rank(m, n)):
        a = _smallest_disagreement(cmask, target_mask, n)
        groups.append({
            "computed_mask": cmask,
            "assignment": a,
            "circuit_output": (cmask >> a) & 1,
            "target_output": (target_mask >> a) & 1,
            "description_ids": by_mask[cmask],
        })
    return {
        "format": CERT_FORMAT,
        "kind": "grouped-by-truth-table",
        "n": n,
        "s": s,
        "target_mask": target_mask,
        "target_truth_vector": truth_vector(target_mask, n),
        "num_descriptions": len(descriptions),
        "num_distinct_computed": len(by_mask),
        "truth_table_bits": truth_table_bits(n),
        "groups": groups,
    }


# Alias.
grouped_certificate = build_grouped_certificate


def verify_grouped_certificate_detailed(
        cert, max_descriptions: int = DEFAULT_MAX_DESCRIPTIONS) -> dict:
    """Strictly verify a grouped certificate, including full coverage.

    The checker re-enumerates all descriptions, requires the groups'
    ``description_ids`` to partition exactly ``0..D-1`` with no duplicates
    and no omissions, re-evaluates every covered description's *whole*
    truth table by Boolean simulation (counting those gate operations),
    and checks each group's assignment really disagrees with the target.
    A rows-only grouped list with no coverage IDs is rejected. Each
    computed mask must occur in exactly one group. As with the naive
    checker, validity proves non-computability, not lexicographic minimality.
    """
    result = {"valid": False, "reason": None, "rows_checked": 0,
              "descriptions_expected": 0, "checker_gate_operations": 0,
              "checker_literal_operations": 0}

    def fail(reason):
        result["reason"] = reason
        return result

    try:
        _validate_max_descriptions(max_descriptions)
    except ValueError as exc:
        return fail(str(exc))
    header = _check_header(cert, "grouped-by-truth-table", _GROUPED_TOP_KEYS)
    if header is None:
        return fail("malformed certificate header")
    n, s, target = header
    count = description_count(n, s)
    if count > max_descriptions:
        return fail("description count %d exceeds cap %d; refused"
                    % (count, max_descriptions))
    if (not _is_int(cert.get("num_descriptions"))
            or cert["num_descriptions"] != count):
        return fail("num_descriptions does not match exact description count")
    descriptions = enumerate_descriptions(n, s, max_descriptions)
    result["descriptions_expected"] = count
    groups = cert.get("groups")
    if not isinstance(groups, list) or not groups:
        return fail("groups must be a nonempty list")
    if (not _is_int(cert.get("num_distinct_computed"))
            or cert["num_distinct_computed"] != len(groups)):
        return fail("num_distinct_computed does not match number of groups")
    seen_masks: set[int] = set()
    seen: set[int] = set()
    gate_ops = 0
    for group in groups:
        if not isinstance(group, dict) or set(group.keys()) != _GROUP_KEYS:
            return fail("malformed group (coverage IDs are required)")
        cmask = group["computed_mask"]
        if not _is_int(cmask) or not 0 <= cmask < num_functions(n):
            return fail("group computed_mask out of range")
        if cmask == target:
            return fail("a group computes the target; no disagreement exists")
        if cmask in seen_masks:
            return fail("duplicate group computed_mask %d" % cmask)
        seen_masks.add(cmask)
        a = group["assignment"]
        if not _is_int(a) or not 0 <= a < (1 << n):
            return fail("group assignment out of range")
        if not _is_int(group["circuit_output"]) or group["circuit_output"] not in (0, 1):
            return fail("group circuit_output is not a bit")
        if not _is_int(group["target_output"]) or group["target_output"] not in (0, 1):
            return fail("group target_output is not a bit")
        if ((cmask >> a) & 1) != group["circuit_output"]:
            return fail("group circuit_output does not match computed_mask")
        if ((target >> a) & 1) != group["target_output"]:
            return fail("group target_output does not match target table")
        if group["circuit_output"] == group["target_output"]:
            return fail("group assignment is not a disagreement")
        ids = group["description_ids"]
        if not isinstance(ids, list) or not ids:
            return fail("group has empty or malformed coverage ID list")
        for rid in ids:
            if not _is_int(rid) or not 0 <= rid < count:
                return fail("coverage id out of range")
            if rid in seen:
                return fail("duplicate coverage id %d" % rid)
            seen.add(rid)
            desc = descriptions[rid]
            # Full-table Boolean re-evaluation of this covered description.
            mask = 0
            for aa in range(1 << n):
                gate_ops += len(desc.gates)
                if evaluate_bool(n, desc.gates, desc.output, aa):
                    mask |= 1 << aa
            if mask != cmask:
                return fail("coverage id %d does not compute its group's mask" % rid)
        result["rows_checked"] += 1
    if seen != set(range(count)):
        return fail("coverage ids do not cover every enumerated description")
    result["checker_gate_operations"] = gate_ops
    result["checker_literal_operations"] = 2 * gate_ops
    result["valid"] = True
    return result


def verify_grouped_certificate(cert,
                               max_descriptions: int = DEFAULT_MAX_DESCRIPTIONS
                               ) -> bool:
    """True iff ``cert`` is a complete, correct grouped certificate."""
    try:
        return verify_grouped_certificate_detailed(cert, max_descriptions)["valid"]
    except Exception:
        return False


# ---------------------------------------------------------------------------
# Partial-coverage counterexample (finite, explicit)
# ---------------------------------------------------------------------------

def partial_coverage_counterexample() -> dict:
    """A finite disproof of 'partial coverage certifies a lower bound'.

    At n=2, s=1 the target NAND (mask 7) *is* computed, by the 1-gate
    description ``NAND(x0, x1)``.  The size-0 descriptions (the inputs)
    each disagree with mask 7 somewhere, so a 'certificate' covering
    only those IDs passes every per-row disagreement check yet the claim
    'no size-<=1 circuit computes 7' is false.  Both strict checkers
    reject such a partial certificate for incompleteness.
    """
    n, s, target = 2, 1, 7
    descriptions = enumerate_descriptions(n, s)
    masks = computed_masks(descriptions, n)
    omitted = [
        {"id": i, "gates": [[a, b] for (a, b) in d.gates], "output": d.output}
        for i, (d, m) in enumerate(zip(descriptions, masks)) if m == target
    ]
    covered_ids = [i for i, d in enumerate(descriptions) if d.size == 0]
    return {
        "n": n, "s": s, "target_mask": target,
        "claim_that_would_be_false": "no size<=1 circuit computes mask 7",
        "covered_description_ids": covered_ids,
        "omitted_descriptions_computing_target": omitted,
        "lesson": (
            "Per-row disagreements over a proper subset of descriptions "
            "certify nothing about the omitted descriptions. Completeness "
            "(every enumeration ID covered exactly once) is essential."
        ),
    }


# ---------------------------------------------------------------------------
# Whole finite experiment
# ---------------------------------------------------------------------------

def run_experiment(n: int, s: int,
                   max_descriptions: int = DEFAULT_MAX_DESCRIPTIONS) -> dict:
    """Run the bounded diagonal experiment for one finite (n, s).

    Returns status ``"OK"`` (missing table found, certificates built),
    ``"NO_MISSING"`` (every function is computed at this size), or
    ``"REFUSED"`` (exact count exceeds the cap; nothing enumerated and
    the missing table is ``"UNKNOWN"``).
    """
    _validate_n_s(n, s)
    _validate_max_descriptions(max_descriptions)
    count = description_count(n, s)
    base = {
        "format": EXPERIMENT_FORMAT,
        "model": {"gate": "NAND (fan-in 2, ordered pairs, repetition allowed)",
                  "assumptions": list(MODEL_ASSUMPTIONS), "scope": SCOPE_NOTE},
        "n": n,
        "s": s,
        "max_descriptions": max_descriptions,
        "description_count_exact": count,
        "descriptions_by_size": {
            str(k): descriptions_of_size_count(n, k) for k in range(s + 1)
        },
        "num_functions_universe": num_functions(n),
        "truth_table_bits": truth_table_bits(n),
        "scope": SCOPE_NOTE,
    }
    if count > max_descriptions:
        return {**base, "status": REFUSED, "missing_status": UNKNOWN,
                "reason": ("exact description count %d exceeds "
                           "max_descriptions=%d; refused before enumeration"
                           % (count, max_descriptions)),
                "num_descriptions_enumerated": 0,
                "num_distinct_computed": None, "missing_mask": None,
                "missing_truth_vector": None, "certificate": None,
                "grouped_certificate": None, "certificate_metrics": None,
                "comparison": None}
    descriptions = enumerate_descriptions(n, s, max_descriptions)
    masks = computed_masks(descriptions, n)
    distinct = set(masks)
    missing = first_missing_mask(distinct, n)
    base.update({
        "num_descriptions_enumerated": len(descriptions),
        "enumeration_count_matches_exact": len(descriptions) == count,
        "num_distinct_computed": len(distinct),
        "computed_masks_lex_order": sorted(distinct, key=lambda m: lex_rank(m, n)),
    })
    if missing is None:
        return {**base, "status": "NO_MISSING", "missing_status": "NONE",
                "reason": "every truth table is computed by a size<=s description",
                "missing_mask": None, "missing_truth_vector": None,
                "certificate": None, "grouped_certificate": None,
                "certificate_metrics": None, "comparison": None}
    cert = build_certificate(n, s, missing, max_descriptions)
    grouped = build_grouped_certificate(n, s, missing, max_descriptions)
    naive_m = certificate_metrics(cert, max_descriptions)
    grouped_m = certificate_metrics(grouped, max_descriptions)
    rows_only = {**grouped,
                 "groups": [{k: v for k, v in g.items()
                             if k != "description_ids"} for g in grouped["groups"]]}
    comparison = {
        "naive_rows": naive_m["num_rows"],
        "naive_certificate_bytes": naive_m["certificate_bytes"],
        "naive_checker_gate_operations": naive_m["checker_gate_operations"],
        "grouped_distinct_functions": len(distinct),
        "grouped_rows": grouped_m["num_rows"],
        "grouped_certificate_bytes_with_coverage": grouped_m["certificate_bytes"],
        "grouped_certificate_bytes_rows_only_no_coverage":
            len(canonical_json_bytes(rows_only)),
        "grouped_checker_gate_operations":
            grouped_m["checker_gate_operations"],
        "note": (
            "Grouping replaces one row per description with one row per "
            "distinct computed truth table, but soundness still needs "
            "coverage of every description: either the certificate lists "
            "every covered ID (so its size still grows with the number of "
            "descriptions) or the checker re-enumerates and re-evaluates "
            "every description itself (exponential checker work). "
            "Neither makes it automatically a polynomial-size NP "
            "certificate with a polynomial-time checker."),
    }
    return {**base, "status": "OK", "missing_status": "FOUND", "reason": None,
            "missing_mask": missing,
            "missing_truth_vector": truth_vector(missing, n),
            "certificate": cert, "grouped_certificate": grouped,
            "certificate_metrics": naive_m,
            "grouped_certificate_metrics": grouped_m,
            "comparison": comparison}


# Alias.
diagonal_experiment = run_experiment


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main(argv=None) -> int:
    p = argparse.ArgumentParser(
        description="Bounded exact diagonal hard-truth-table experiment")
    p.add_argument("--n", type=int, default=2)
    p.add_argument("--s", type=int, default=3)
    p.add_argument("--max-descriptions", type=int,
                   default=DEFAULT_MAX_DESCRIPTIONS)
    p.add_argument("--output", default=None,
                   help="write the full experiment JSON to this path")
    args = p.parse_args(argv)
    try:
        result = run_experiment(args.n, args.s, args.max_descriptions)
    except ValueError as exc:
        print("error: %s" % exc, file=sys.stderr)
        return 2
    text = json.dumps(result, indent=2)
    if args.output:
        with open(args.output, "w", encoding="utf-8") as fh:
            fh.write(text + "\n")
        summary = {k: result[k] for k in (
            "n", "s", "status", "description_count_exact",
            "num_descriptions_enumerated", "num_distinct_computed",
            "missing_mask") if k in result}
        print(json.dumps(summary, indent=2))
        print("wrote %s" % args.output)
    else:
        print(text)
    return 0 if result["status"] in ("OK", "NO_MISSING") else 2


if __name__ == "__main__":
    raise SystemExit(main())
