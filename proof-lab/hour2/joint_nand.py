"""Exact finite shared-output NAND costs; n=1 or 2, no free constants."""
from __future__ import annotations

from collections import deque
import hashlib
import json
from pathlib import Path

MAX_STATES = 16384
MAX_TRANSITIONS = 2_000_000


def _integer(value, low, high):
    return type(value) is int and low <= value <= high


def _inputs(n):
    return tuple(sum(1 << a for a in range(1 << n) if (a >> i) & 1)
                 for i in range(n))


def one_gate_targets(n):
    """Deduplicate all ordered primary-input NAND pairs by truth function."""
    if not _integer(n, 1, 2):
        raise ValueError("n must be an exact integer 1 or 2")
    primary, full = _inputs(n), (1 << (1 << n)) - 1
    return sorted({full ^ (a & b) for a in primary for b in primary})


def verify_witness(witness, targets, expected_cost=None):
    """Independent per-assignment Boolean simulation of a supplied DAG."""
    if type(witness) is not dict or set(witness) != {"n", "gates", "outputs"}:
        return False
    n, gates, outputs = (witness[k] for k in ("n", "gates", "outputs"))
    if not _integer(n, 1, 2) or type(gates) is not list or len(gates) > 16:
        return False
    if type(outputs) is not list or type(targets) is not list:
        return False
    if not 1 <= len(outputs) == len(targets) <= 2:
        return False
    if expected_cost is not None and (
            not _integer(expected_cost, 0, 16) or len(gates) != expected_cost):
        return False
    full = (1 << (1 << n)) - 1
    if any(not _integer(t, 0, full) for t in targets):
        return False
    for k, pair in enumerate(gates):
        if type(pair) is not list or len(pair) != 2:
            return False
        if any(not _integer(i, 0, n + k - 1) for i in pair):
            return False
    if any(not _integer(i, 0, n + len(gates) - 1) for i in outputs):
        return False
    observed = [0] * len(outputs)
    for assignment in range(1 << n):
        signals = [bool((assignment >> i) & 1) for i in range(n)]
        for left, right in gates:
            signals.append(not (signals[left] and signals[right]))
        for k, output in enumerate(outputs):
            if signals[output]:
                observed[k] += 1 << assignment
    return observed == targets


def _witness(n, state, targets, parents):
    path = []
    while parents[state] is not None:
        previous, a, b, value = parents[state]
        path.append((a, b, value))
        state = previous
    indices = {mask: i for i, mask in enumerate(_inputs(n))}
    gates = []
    for a, b, value in reversed(path):
        gates.append([indices[a], indices[b]])
        indices[value] = n + len(gates) - 1
    result = {"n": n, "gates": gates, "outputs": [indices[t] for t in targets]}
    if not verify_witness(result, targets, len(path)):
        raise AssertionError("independent witness verification failed")
    return result


def compute_all(n=2, *, max_states=MAX_STATES, max_transitions=MAX_TRANSITIONS):
    """Exhaust semantic states. Any resource refusal yields UNKNOWN, no minima."""
    if not _integer(n, 1, 2):
        return {"status": "MALFORMED", "reason": "n_must_be_1_or_2"}
    if not _integer(max_states, 1, MAX_STATES) or not _integer(
            max_transitions, 0, MAX_TRANSITIONS):
        return {"status": "MALFORMED", "reason": "invalid_resource_cap"}
    full, primary = (1 << (1 << n)) - 1, _inputs(n)
    gs = one_gate_targets(n)
    start = frozenset(primary)
    parents, queue = {start: None}, deque([start])
    single_states, joint_states = {}, {}
    transitions, expanded = 0, 0

    def remember(state):
        for f in sorted(state):
            single_states.setdefault(f, state)
            for g in gs:
                if g in state:
                    joint_states.setdefault((f, g), state)

    def unknown(reason):
        return {"status": "UNKNOWN", "reason": reason, "n": n,
                "states_discovered": len(parents), "states_expanded": expanded,
                "transitions": transitions, "single_costs": None, "joint": None,
                "scope": "Resource refusal; no exact minima claimed."}

    remember(start)
    while queue:
        state = queue.popleft()
        available = sorted(state)
        for i, a in enumerate(available):
            for b in available[i:]:
                if transitions >= max_transitions:
                    return unknown("transition_cap")
                transitions += 1
                value = full ^ (a & b)
                if value in state:
                    continue
                next_state = state | {value}
                if next_state in parents:
                    continue
                if len(parents) >= max_states:
                    return unknown("state_cap")
                parents[next_state] = (state, a, b, value)
                queue.append(next_state)
                remember(next_state)
        expanded += 1
    if len(single_states) != full + 1 or len(joint_states) != (full + 1) * len(gs):
        raise AssertionError("complete finite search omitted a target")
    singles, joint = [], []
    for f in range(full + 1):
        witness = _witness(n, single_states[f], [f], parents)
        singles.append({"f": f, "cost": len(witness["gates"]), "witness": witness})
        for g in gs:
            witness = _witness(n, joint_states[f, g], [f, g], parents)
            joint.append({"f": f, "g": g, "cost": len(witness["gates"]),
                          "witness": witness})
    costs = [entry["cost"] for entry in singles]
    groups = {}
    for entry in joint:
        profile = tuple(combination_profile(n, entry["f"], entry["g"], costs))
        groups.setdefault(profile, []).append(
            {"f": entry["f"], "g": entry["g"], "joint_cost": entry["cost"]})
    collisions = [{"profile": list(profile), "pairs": pairs}
                  for profile, pairs in sorted(groups.items())
                  if len({pair["joint_cost"] for pair in pairs}) > 1]
    return {"status": "EXACT", "n": n, "one_gate_targets": gs,
            "states_discovered": len(parents), "states_expanded": expanded,
            "transitions": transitions, "single_costs": costs, "singles": singles,
            "joint": joint, "profile_count": len(groups),
            "same_profile_different_joint_cost": collisions,
            "scope": "Finite exhaustive computation in this NAND model only; no general reduction or P-vs-NP conclusion."}


def combination_mask(n, f, g, h):
    """h indexes (fbit + 2*gbit); h itself is a two-input truth mask."""
    if not _integer(n, 1, 2):
        raise ValueError("n must be 1 or 2")
    full = (1 << (1 << n)) - 1
    if not all(_integer(value, 0, full) for value in (f, g)) or not _integer(h, 0, 15):
        raise ValueError("invalid truth mask")
    return sum(((h >> (((f >> a) & 1) + 2 * ((g >> a) & 1))) & 1) << a
               for a in range(1 << n))


def combination_profile(n, f, g, costs):
    """Return all 16 scalar costs C(h(f,g)); no inference about J is made."""
    if not _integer(n, 1, 2):
        raise ValueError("n must be 1 or 2")
    if type(costs) is not list or len(costs) != 1 << (1 << n) or any(
            not _integer(value, 0, 16) for value in costs):
        raise ValueError("expected exact finite cost table")
    return [costs[combination_mask(n, f, g, h)] for h in range(16)]


def source_sha256_lf(raw=None):
    if raw is None:
        raw = Path(__file__).read_bytes()
    if type(raw) is not bytes:
        raise ValueError("source bytes required")
    return hashlib.sha256(raw.replace(b"\r\n", b"\n").replace(b"\r", b"\n")).hexdigest()


def build_report(n=2):
    result = compute_all(n)
    result["source_sha256_lf"] = source_sha256_lf()
    result["source_hash_normalization"] = "CRLF and CR converted to LF before SHA-256"
    result["truth_table_convention"] = "assignment a has xi=(a>>i)&1; bit a is the output"
    result["model"] = "Binary NAND, repeated fanins, free fanout, primary inputs only, no free constants; cost is shared DAG gate count."
    result["profile_order"] = "h=0..15; h index=fbit+2*gbit; entries are C(h(f,g))"
    return result


if __name__ == "__main__":
    print(json.dumps(build_report(), indent=2, sort_keys=True))
