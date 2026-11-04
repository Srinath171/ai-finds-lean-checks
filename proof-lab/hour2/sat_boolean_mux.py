"""Independent Boolean/one-hot finite NAND encoding; solver evidence only."""
from __future__ import annotations

import hashlib
import itertools
import json
from pathlib import Path
import time


def _integer(value, low, high):
    return type(value) is int and low <= value <= high


def verify_witness(n, target, witness):
    """Independent assignment evaluator; no solver expressions or mask gates."""
    if not _integer(n, 1, 3) or not _integer(target, 0, (1 << (1 << n)) - 1):
        return False
    if type(witness) is not dict or set(witness) != {"gates", "output"}:
        return False
    gates, output = witness["gates"], witness["output"]
    if type(gates) is not list or len(gates) > 7 or not _integer(output, 0, n + len(gates) - 1):
        return False
    for k, pair in enumerate(gates):
        if type(pair) is not list or len(pair) != 2 or any(
                not _integer(i, 0, n + k - 1) for i in pair):
            return False
    observed = []
    for assignment in range(1 << n):
        signals = [bool((assignment >> i) & 1) for i in range(n)]
        for left, right in gates:
            signals.append(not (signals[left] and signals[right]))
        observed.append(signals[output])
    return all(value == bool((target >> a) & 1) for a, value in enumerate(observed))


def solve_at_most(n, target, gate_bound, *, timeout_ms=30000):
    """Boolean CNF encoding, no Int/BitVec selectors. UNKNOWN remains unknown."""
    if not _integer(n, 1, 3) or not _integer(target, 0, (1 << (1 << n)) - 1):
        raise ValueError("invalid input count or truth mask")
    if not _integer(gate_bound, 0, 7) or not _integer(timeout_ms, 1, 60000):
        raise ValueError("invalid gate bound or timeout")
    import z3
    solver = z3.Solver()
    solver.set(timeout=timeout_ms, random_seed=0)
    rows = 1 << n
    signals = [[z3.BoolVal(bool((a >> i) & 1)) for a in range(rows)] for i in range(n)]
    choices = []
    clauses = 0
    def add(*terms):
        nonlocal clauses
        solver.add(z3.Or(*terms))
        clauses += 1
    def exactly_one(variables):
        add(*variables)
        for left, right in itertools.combinations(variables, 2):
            add(z3.Not(left), z3.Not(right))
    for k in range(gate_bound):
        truth = [z3.Bool(f"value_{k}_{a}") for a in range(rows)]
        pairs = list(itertools.combinations_with_replacement(range(n + k), 2))
        selectors = [z3.Bool(f"pair_{k}_{left}_{right}") for left, right in pairs]
        exactly_one(selectors)
        for selector, (left, right) in zip(selectors, pairs):
            for a in range(rows):
                # selector => truth = NAND(left,right), three direct CNF clauses.
                add(z3.Not(selector), truth[a], signals[left][a])
                add(z3.Not(selector), truth[a], signals[right][a])
                add(z3.Not(selector), z3.Not(truth[a]),
                    z3.Not(signals[left][a]), z3.Not(signals[right][a]))
        signals.append(truth)
        choices.append((pairs, selectors))
    outputs = [z3.Bool(f"output_{i}") for i in range(len(signals))]
    exactly_one(outputs)
    for i, selector in enumerate(outputs):
        for a in range(rows):
            add(z3.Not(selector), signals[i][a] if ((target >> a) & 1) else z3.Not(signals[i][a]))
    started = time.monotonic()
    verdict = solver.check()
    result = {"n": n, "target": target, "gate_bound": gate_bound,
              "status": str(verdict).upper(), "timeout_ms": timeout_ms,
              "elapsed_seconds": round(time.monotonic() - started, 6),
              "clauses": clauses, "z3_version": z3.get_version_string(),
              "encoding": "Boolean truth bits; pairwise one-hot predecessor pairs and output selector; NAND CNF",
              "claim_scope": "Bounded solver evidence, not a formally checked lower-bound proof"}
    if verdict == z3.sat:
        model = solver.model()
        gates = []
        for pairs, selectors in choices:
            selected = [pair for pair, s in zip(pairs, selectors) if z3.is_true(model.eval(s))]
            if len(selected) != 1:
                raise AssertionError("non-one-hot solver witness")
            gates.append(list(selected[0]))
        selected_outputs = [i for i, s in enumerate(outputs) if z3.is_true(model.eval(s))]
        if len(selected_outputs) != 1:
            raise AssertionError("non-one-hot output")
        witness = {"gates": gates, "output": selected_outputs[0]}
        if not verify_witness(n, target, witness):
            raise AssertionError("independent witness rejection")
        result.update(witness=witness, witness_independently_verified=True)
    elif verdict == z3.unknown:
        result["reason"] = "solver_timeout_or_unknown"
    return result


def source_sha256_lf():
    raw = Path(__file__).read_bytes().replace(b"\r\n", b"\n").replace(b"\r", b"\n")
    return hashlib.sha256(raw).hexdigest()


def run_corroboration():
    results = []
    for target in (118, 126):
        for bound in (6, 7):
            result = solve_at_most(3, target, bound)
            results.append(result)
            print(json.dumps(result), flush=True)
    return {"source_sha256_lf": source_sha256_lf(),
            "source_hash_normalization": "CRLF and CR converted to LF",
            "model": "Primary inputs only, no free constants, repeated NAND fanins and free fanout, unrestricted output signal",
            "at_most_justification": "Any shorter circuit can be padded with unused NAND gates; output is free to select any input or gate. No duplicate or unused-gate restrictions.",
            "lower_bound_scope": "Independent encoding corroboration from Z3 only; not an independent solver and not a Lean proof",
            "results": results}


if __name__ == "__main__":
    print(json.dumps(run_corroboration(), indent=2, sort_keys=True))
