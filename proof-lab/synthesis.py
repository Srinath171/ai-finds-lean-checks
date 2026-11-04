"""Exact bounded NAND circuit synthesis with z3.

UNSAT results are z3 solver evidence for the stated bounded model, not formal proofs.
Truth tables: bit j of a table is the function value on assignment j, where input i = (j >> i) & 1.
"""
import argparse
import json
import sys

import z3

MAX_N, MAX_GATES, MAX_TIMEOUT_MS = 4, 8, 600_000
EVIDENCE = "z3 solver result for the bounded model (solver evidence, not a formal proof)"


def _is_int(x):
    return type(x) is int  # rejects bool, float, and int subclasses


def _check(n, target, k=None, timeout_ms=None):
    if not _is_int(n) or not 1 <= n <= MAX_N:
        raise ValueError(f"n must be an int in 1..{MAX_N}")
    if not _is_int(target) or not 0 <= target < 1 << (1 << n):
        raise ValueError(f"target must be an int in [0, 2^{1 << n})")
    if k is not None and (not _is_int(k) or not 0 <= k <= MAX_GATES):
        raise ValueError(f"gate budget must be an int in 0..{MAX_GATES}")
    if timeout_ms is not None and (not _is_int(timeout_ms) or not 1 <= timeout_ms <= MAX_TIMEOUT_MS):
        raise ValueError(f"timeout_ms must be an int in 1..{MAX_TIMEOUT_MS}")


def input_table(n, i):
    return sum(((j >> i) & 1) << j for j in range(1 << n))


def evaluate(n, witness):
    """Independent pure-Python evaluator over every assignment. Raises ValueError if malformed."""
    _check(n, 0)
    if not isinstance(witness, dict):
        raise ValueError("witness must be a dict")
    gates, out = witness.get("gates"), witness.get("output")
    if not isinstance(gates, list) or len(gates) > MAX_GATES:
        raise ValueError("gates must be a list within the cap")
    for i, g in enumerate(gates):
        if not isinstance(g, (list, tuple)) or len(g) != 2:
            raise ValueError(f"gate {i} must be a pair")
        if not all(_is_int(x) and 0 <= x < n + i for x in g):
            raise ValueError(f"gate {i} predecessors must be ints in [0, {n + i})")
    if not _is_int(out) or not 0 <= out < n + len(gates):
        raise ValueError("output index out of range")
    table = 0
    for j in range(1 << n):
        vals = [(j >> i) & 1 for i in range(n)]
        for a, b in gates:
            vals.append(1 - (vals[a] & vals[b]))
        table |= vals[out] << j
    return table


def verify(n, target, witness):
    _check(n, target)
    try:
        return evaluate(n, witness) == target
    except ValueError:
        return False


def synthesize(n, target, k, timeout_ms=10_000):
    _check(n, target, k, timeout_ms)
    w = 1 << n
    vals = [z3.BitVecVal(input_table(n, i), w) for i in range(n)]
    s = z3.Solver()
    s.set("timeout", timeout_ms)

    def pick(idx, m):
        e = vals[m - 1]
        for c in range(m - 2, -1, -1):
            e = z3.If(idx == c, vals[c], e)
        return e

    choices = []
    for i in range(k):
        m = n + i
        a, b = z3.Int(f"a{i}"), z3.Int(f"b{i}")
        s.add(0 <= a, a <= b, b < m)  # a <= b is sound: NAND is commutative
        vals.append(~(pick(a, m) & pick(b, m)))
        choices.append((a, b))
    o = z3.Int("out")
    s.add(0 <= o, o < n + k, pick(o, n + k) == z3.BitVecVal(target, w))
    r = s.check()
    base = {"n": n, "target": target, "k": k, "evidence": EVIDENCE}
    if r == z3.sat:
        mdl = s.model()
        val = lambda v: mdl.eval(v, model_completion=True).as_long()
        witness = {"gates": [[val(a), val(b)] for a, b in choices], "output": val(o)}
        if verify(n, target, witness):
            return {**base, "status": "SAT", "witness": witness}
        return {**base, "status": "UNKNOWN", "reason": "solver witness failed independent verification"}
    if r == z3.unsat:
        return {**base, "status": "UNSAT"}
    return {**base, "status": "UNKNOWN", "reason": str(s.reason_unknown())}


def minimum(n, target, max_gates, timeout_ms=10_000, k0=0):
    _check(n, target, max_gates, timeout_ms)
    if not _is_int(k0) or not 0 <= k0 <= max_gates:
        raise ValueError("k0 must be an int in 0..max_gates")
    metadata = {"n": n, "target": target, "max_gates": max_gates, "timeout_ms_per_query": timeout_ms, "z3_version": z3.get_full_version()}
    lower_all_unsat = k0 == 0
    attempts = []
    for k in range(k0, max_gates + 1):
        r = synthesize(n, target, k, timeout_ms)
        attempts.append({"k": k, "status": r["status"]})
        if r["status"] == "SAT":
            return {**metadata, "status": "SAT", "gates": k, "exact": lower_all_unsat, "witness": r["witness"],
                    "attempts": attempts, "evidence": EVIDENCE}
        if r["status"] != "UNSAT":
            lower_all_unsat = False
    status = "UNSAT" if all(a["status"] == "UNSAT" for a in attempts) else "UNKNOWN"
    return {**metadata, "status": status, "exact": False, "attempts": attempts, "evidence": EVIDENCE}


def main(argv=None):
    p = argparse.ArgumentParser(description="Bounded exact NAND synthesis (UNSAT = solver evidence).")
    p.add_argument("--n", type=int, required=True)
    p.add_argument("--target", required=True, help="truth table as int (decimal, 0x.., 0b..)")
    p.add_argument("--max-gates", type=int, required=True)
    p.add_argument("--timeout-ms", type=int, default=10_000)
    p.add_argument("--output", help="new JSON file to create (existing files are never overwritten)")
    args = p.parse_args(argv)
    try:
        if len(args.target) > 32:
            raise ValueError("target string too long")
        res = minimum(args.n, int(args.target, 0), args.max_gates, args.timeout_ms)
    except ValueError as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    text = json.dumps(res, indent=2)
    if args.output:
        try:
            with open(args.output, "x", encoding="utf-8") as f:
                f.write(text + "\n")
        except OSError as e:
            print(f"error: cannot write output: {e}", file=sys.stderr)
            return 2
    print(text)
    return 0 if res["status"] == "SAT" else 1


if __name__ == "__main__":
    sys.exit(main())
