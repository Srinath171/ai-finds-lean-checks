"""Exact finite NAND circuit lower-bound lab.

Model (fixed throughout this module)
------------------------------------
* Inputs are the variables x0, ..., x_{n-1} only.
* NO free constants (0 / 1 are not available as signals unless built).
* NO free complemented inputs (NOT xi is not available unless built).
* The only gate is binary NAND.  Fan-in is exactly two and repetition is
  allowed, i.e. NAND(s, s) = NOT s is a legal gate.
* Fanout is unlimited: a computed signal may feed any number of later
  gates (DAG sharing).  Circuits are therefore DAGs, not trees/formulas.
* The output may be any input or any computed signal.  Circuit size is
  the number of NAND gates.

Truth tables are bit masks.  There are 2**n input assignments, indexed
by a in [0, 2**n); bit i of a is the value of xi on assignment a.  A
function's mask has bit a set iff the function is 1 on assignment a.
For n = 2 this gives x0 = 0b1010, x1 = 0b1100, XOR = 0b0110,
XNOR = 0b1001 (assignment order 00, 10, 01, 11 for (x0, x1)).

Method
------
Minimal sizes are found by breadth-first search over STATES.  A state
is the SET of truth-table masks available after some gates have been
built (the inputs plus every distinct function computed so far).  From a
state, one more gate adds NAND(u, v) for u, v already in the state
(repetition allowed); if that function is already present the gate is a
duplicate and is omitted.  Omitting duplicate functional signals is
sound: such a gate changes neither the set of available functions nor
what any later gate can compute, so deleting it from any circuit never
hurts.  Because a state records the whole set of shared subfunctions,
DAG sharing is preserved exactly.  We never use an independent
single-function cost recurrence (which would price shared subcircuits
more than once and lose sharing).

BFS expands states layer by layer, where layer d holds states with
exactly d gates.  The first layer in which a function appears in any
state is its exact minimum size, and parent pointers give a
reconstructable witness circuit for every reached function.  Every
witness is re-verified by an independent per-assignment Boolean
simulation that shares no code with the mask-based search.

Caps and UNKNOWN
----------------
For n = 3 the state space is far too large to exhaust, so the search
accepts strict caps (max gates / depth, max states, max states per
layer, max expanded nodes, wall-time timeout).  Functions not reached when a
cap stops the search are reported as UNKNOWN (never as a number).
``completed_layers`` counts only gate layers whose states were fully
generated; no lower bound beyond a fully completed layer is ever
claimed: an unreached function is only known to need more gates than
``completed_layers`` when the search was cut, and exactly its recorded
cost when a witness was found.

This module makes exact finite statements only (here: n = 2 fully, and
whatever an explicitly capped n = 3 run reaches).  No asymptotic or
general circuit lower-bound claim is made anywhere.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import time
from dataclasses import dataclass, field

UNKNOWN = "UNKNOWN"

MODEL_ASSUMPTIONS = [
    "inputs are the variables x0..x(n-1) only",
    "no free constants: 0 and 1 are not available unless built by gates",
    "no free complemented inputs: NOT xi is not available unless built",
    "only gate is binary NAND; fan-in exactly two; repetition allowed (NAND(s,s) = NOT s)",
    "unlimited fanout: computed signals may be reused by any later gates (DAG sharing)",
    "output may be any input or computed signal; size = number of NAND gates",
    "truth tables are bit masks over assignments a in [0, 2**n), bit i of a = value of xi",
]

SCOPE_NOTE = (
    "Exact finite results for the stated n and caps only. "
    "No asymptotic, superpolynomial, or P-vs-NP claim is made or implied."
)


# ---------------------------------------------------------------------------
# Truth-table masks
# ---------------------------------------------------------------------------

def check_n(n: int) -> int:
    if not isinstance(n, int) or isinstance(n, bool) or n < 1 or n > 3:
        raise ValueError("this lab supports n in {1, 2, 3} for exact search")
    return n


def num_assignments(n: int) -> int:
    return 1 << n


def full_mask(n: int) -> int:
    """Mask with all 2**n truth-table bits set (the constant-1 function)."""
    return (1 << (1 << n)) - 1


def input_masks(n: int) -> tuple[int, ...]:
    """Truth-table masks of x0, ..., x_{n-1}, in that order."""
    check_n(n)
    return tuple(
        sum(1 << a for a in range(1 << n) if (a >> i) & 1) for i in range(n)
    )


def nand_mask(a: int, b: int, n: int) -> int:
    """Truth-table mask of NAND applied pointwise to masks a and b."""
    return full_mask(n) ^ (a & b)


def all_function_masks(n: int) -> range:
    """Every truth-table mask for n inputs (there are 2**(2**n))."""
    check_n(n)
    return range(1 << (1 << n))


def truth_vector(mask: int, n: int) -> list[int]:
    """Output bits in assignment order a = 0, 1, ..., 2**n - 1."""
    return [(mask >> a) & 1 for a in range(1 << n)]


_N2_NAMES = {
    0: "const 0",
    1: "NOR(x0,x1)",
    2: "x0 AND (NOT x1)",
    3: "NOT x1",
    4: "(NOT x0) AND x1",
    5: "NOT x0",
    6: "x0 XOR x1",
    7: "NAND(x0,x1)",
    8: "x0 AND x1",
    9: "x0 XNOR x1",
    10: "x0",
    11: "x1 IMPLIES x0",
    12: "x1",
    13: "x0 IMPLIES x1",
    14: "x0 OR x1",
    15: "const 1",
}


def function_name(mask: int, n: int) -> str:
    if n == 2 and mask in _N2_NAMES:
        return _N2_NAMES[mask]
    return "f_%d" % mask


# ---------------------------------------------------------------------------
# Witnesses: reconstructable wiring, independently verified
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Witness:
    """A concrete NAND circuit.

    Signals 0..n-1 are the inputs x0..x_{n-1}.  Signal n+k is the output
    of gates[k].  Gate k is a pair (i, j) of earlier signal indices
    (i, j < n+k; i == j allowed) meaning NAND(signal_i, signal_j).
    ``output`` is the index of the signal taken as the circuit output.
    """

    n: int
    gates: tuple[tuple[int, int], ...]
    output: int

    @property
    def size(self) -> int:
        return len(self.gates)

    def evaluate_mask(self) -> int:
        """Truth-table mask computed by this circuit (mask arithmetic)."""
        inputs = input_masks(self.n)
        signals = list(inputs)
        for (i, j) in self.gates:
            signals.append(nand_mask(signals[i], signals[j], self.n))
        return signals[self.output]

    def to_dict(self, target: int | None = None) -> dict:
        d = {
            "n": self.n,
            "gates": [[i, j] for (i, j) in self.gates],
            "output": self.output,
            "size": self.size,
        }
        if target is not None:
            d["target"] = target
        return d


def _simulate_per_assignment(n: int, gates, output: int) -> int:
    """Independent evaluation: Boolean simulation assignment by assignment.

    Deliberately uses no mask arithmetic, so it cross-checks both the
    search and the mask evaluator.  Raises ValueError on bad wiring.
    """
    mask = 0
    for a in range(1 << n):
        signals = [bool((a >> i) & 1) for i in range(n)]
        for k, (i, j) in enumerate(gates):
            if not (0 <= i < n + k and 0 <= j < n + k):
                raise ValueError("gate %d references a not-yet-built signal" % k)
            signals.append(not (signals[i] and signals[j]))
        if not (0 <= output < len(signals)):
            raise ValueError("output references a nonexistent signal")
        if signals[output]:
            mask |= 1 << a
    return mask


def verify_witness(witness: Witness, target: int) -> bool:
    """Strict certificate check, with independent Boolean evaluation."""
    if not isinstance(witness, Witness):
        return False
    if type(witness.n) is not int or not 1 <= witness.n <= 3:
        return False
    if type(target) is not int or not 0 <= target < (1 << (1 << witness.n)):
        return False
    if type(witness.output) is not int or not isinstance(witness.gates, (list, tuple)):
        return False
    for k, gate in enumerate(witness.gates):
        if not isinstance(gate, (list, tuple)) or len(gate) != 2:
            return False
        i, j = gate
        if type(i) is not int or type(j) is not int:
            return False
        if not (0 <= i < witness.n + k and 0 <= j < witness.n + k):
            return False
    if not 0 <= witness.output < witness.n + witness.size:
        return False
    return _simulate_per_assignment(witness.n, witness.gates, witness.output) == target


def verify_witness_dict(d: dict) -> bool:
    """Verify exact integer JSON fields; never coerce a different circuit."""
    if not isinstance(d, dict):
        return False
    try:
        n, gates, output, target = d["n"], d["gates"], d["output"], d["target"]
        if not isinstance(gates, (list, tuple)):
            return False
        if "size" in d and (type(d["size"]) is not int or d["size"] != len(gates)):
            return False
        return verify_witness(Witness(n=n, gates=gates, output=output), target)
    except KeyError:
        return False


# ---------------------------------------------------------------------------
# Breadth-first search over sets of available truth tables
# ---------------------------------------------------------------------------

@dataclass
class SearchResult:
    n: int
    costs: dict[int, int | None]          # mask -> exact size, or None = UNKNOWN
    witnesses: dict[int, Witness | None]  # mask -> witness, or None
    completed_layers: int                 # gate layers fully generated
    states_per_layer: list[int]           # states generated at each layer
    visited_states: int
    expanded_nodes: int
    truncated: bool
    truncation_reason: str | None
    caps: dict = field(default_factory=dict)

    def cost_or_unknown(self, mask: int):
        c = self.costs.get(mask)
        return UNKNOWN if c is None else c

    def to_dict(self) -> dict:
        functions = []
        for mask in all_function_masks(self.n):
            w = self.witnesses.get(mask)
            functions.append(
                {
                    "mask": mask,
                    "truth_vector": truth_vector(mask, self.n),
                    "name": function_name(mask, self.n),
                    "cost": self.cost_or_unknown(mask),
                    "witness": (w.to_dict(target=mask) if w is not None else None),
                }
            )
        return {
            "model": {
                "gate": "NAND (fan-in 2, repetition allowed)",
                "assumptions": list(MODEL_ASSUMPTIONS),
                "scope": SCOPE_NOTE,
            },
            "n": self.n,
            "input_masks": list(input_masks(self.n)),
            "num_functions": 1 << (1 << self.n),
            "exhausted_all_functions": all(
                c is not None for c in self.costs.values()
            ),
            "truncated": self.truncated,
            "truncation_reason": self.truncation_reason,
            "completed_layers": self.completed_layers,
            "states_per_layer": list(self.states_per_layer),
            "visited_states": self.visited_states,
            "expanded_nodes": self.expanded_nodes,
            "caps": dict(self.caps),
            "functions": functions,
        }


def _available(state: int) -> list[int]:
    """Function masks present in a state bitset (bit f set iff f available)."""
    out = []
    s = state
    while s:
        low = s & (-s)
        out.append(low.bit_length() - 1)
        s ^= low
    return out


def search(
    n: int,
    max_gates: int | None = None,
    max_states: int | None = None,
    max_states_per_layer: int | None = None,
    max_nodes: int | None = None,
    timeout_seconds: float | None = None,
) -> SearchResult:
    """BFS over sets of available truth tables; exact minima + witnesses.

    Default for n = 2 is exhaustive (no effective caps).  Default for
    n = 3 is strictly capped; pass explicit caps to change the budget.
    Unreached functions get cost None (reported as UNKNOWN).
    """
    check_n(n)
    universe = 1 << (1 << n)
    if max_gates is None:
        max_gates = universe if n == 2 else 6
    if max_states is None:
        max_states = 1_000_000 if n == 2 else 100_000
    if max_states_per_layer is None:
        max_states_per_layer = max_states
    if max_nodes is None:
        max_nodes = max_states
    if timeout_seconds is None:
        timeout_seconds = 600.0 if n == 2 else 30.0
    for name, value in (("max_gates", max_gates), ("max_states", max_states),
                        ("max_states_per_layer", max_states_per_layer), ("max_nodes", max_nodes)):
        if type(value) is not int or value < 0:
            raise ValueError(f"{name} must be a nonnegative integer")
    if (isinstance(timeout_seconds, bool) or not isinstance(timeout_seconds, (int, float))
            or not math.isfinite(timeout_seconds) or timeout_seconds <= 0):
        raise ValueError("timeout_seconds must be finite and positive")
    caps = {
        "max_gates": max_gates,
        "max_states": max_states,
        "max_states_per_layer": max_states_per_layer,
        "max_nodes": max_nodes,
        "timeout_seconds": timeout_seconds,
    }

    inputs = input_masks(n)
    full = full_mask(n)
    start = 0
    for m in inputs:
        start |= 1 << m

    # A zero state/layer allowance cannot even store the initial state.
    # Input functions still have trivial zero-gate certificates independently.
    if max_states == 0 or max_states_per_layer == 0:
        costs = {m: (0 if m in inputs else None) for m in range(universe)}
        witnesses = {m: (Witness(n, (), inputs.index(m)) if m in inputs else None)
                     for m in range(universe)}
        for m, witness in witnesses.items():
            if witness is not None and not verify_witness(witness, m):
                raise RuntimeError("independent input-witness verification failed")
        return SearchResult(n, costs, witnesses, 0, [0], 0, 0, True,
                            "zero state allowance", caps)

    # parent[state] = (prev_state, u, v, added_function) or None for start.
    parent: dict[int, tuple[int, int, int, int] | None] = {start: None}
    costs: dict[int, int | None] = {m: None for m in range(universe)}
    for m in inputs:
        costs[m] = 0

    def build_witness(state: int, target: int) -> Witness:
        chain = []
        s = state
        while parent[s] is not None:
            prev, u, v, w = parent[s]  # type: ignore[misc]
            chain.append((u, v, w))
            s = prev
        chain.reverse()
        ref: dict[int, int] = {}
        for idx, m in enumerate(inputs):
            ref[m] = idx
        gates = []
        for (u, v, w) in chain:
            gates.append((ref[u], ref[v]))
            ref[w] = n + len(gates) - 1
        return Witness(n=n, gates=tuple(gates), output=ref[target])

    states_per_layer = [1]
    frontier = [start]
    completed_layers = 0
    truncated = False
    reason: str | None = None
    expanded = 0
    start_time = time.monotonic()
    deadline = start_time + timeout_seconds

    def witnesses_snapshot() -> dict[int, Witness | None]:
        return {m: None for m in range(universe)}

    # Map each reached function to a state that contains it (first found).
    found_in: dict[int, int] = {m: start for m in inputs}

    depth = 0
    while True:
        # Also check before declaring exhaustive completion: small searches
        # must obey deadlines just like large searches.
        if time.monotonic() >= deadline:
            truncated = True
            reason = "wall-time timeout %.3fs reached" % timeout_seconds
            completed_layers = depth
            break
        if all(c is not None for c in costs.values()):
            completed_layers = depth
            break
        if depth >= max_gates:
            truncated = True
            reason = "depth cap max_gates=%d reached" % max_gates
            completed_layers = depth
            break

        next_frontier: list[int] = []
        cut = False
        for state in frontier:
            if expanded >= max_nodes:
                truncated, cut = True, True
                reason = "node cap max_nodes=%d reached" % max_nodes
                break
            if time.monotonic() >= deadline:
                truncated, cut = True, True
                reason = "wall-time timeout %.3fs reached" % timeout_seconds
                break
            expanded += 1
            avail = _available(state)
            for ii in range(len(avail)):
                u = avail[ii]
                for jj in range(ii, len(avail)):
                    if time.monotonic() >= deadline:
                        truncated, cut = True, True
                        reason = "wall-time timeout %.3fs reached" % timeout_seconds
                        break
                    v = avail[jj]
                    w = full ^ (u & v)
                    if state >> w & 1:
                        continue  # duplicate functional signal: omit soundly
                    new_state = state | (1 << w)
                    if new_state in parent:
                        continue
                    # Enforce storage limits before insertion, including a
                    # limit of one (the initial state already uses that slot).
                    if len(parent) >= max_states:
                        truncated, cut = True, True
                        reason = "state cap max_states=%d reached" % max_states
                        break
                    if len(next_frontier) >= max_states_per_layer:
                        truncated, cut = True, True
                        reason = (
                            "per-layer state cap max_states_per_layer=%d reached"
                            % max_states_per_layer
                        )
                        break
                    parent[new_state] = (state, u, v, w)
                    next_frontier.append(new_state)
                    if costs[w] is None:
                        costs[w] = depth + 1
                        found_in[w] = new_state
                if cut:
                    break
            if cut:
                break

        if cut:
            # The layer being generated (depth+1) is only partial: it does
            # not count as completed.  Costs already recorded still carry
            # witnesses, so they stay exact; the rest remain UNKNOWN.
            states_per_layer.append(len(next_frontier))
            completed_layers = depth
            break

        states_per_layer.append(len(next_frontier))
        completed_layers = depth + 1
        if not next_frontier:
            completed_layers = depth
            break
        frontier = next_frontier
        depth += 1

    witnesses: dict[int, Witness | None] = witnesses_snapshot()
    for m, st in found_in.items():
        witness = build_witness(st, m)
        if witness.size != costs[m] or not verify_witness(witness, m):
            raise RuntimeError("independent witness verification failed")
        witnesses[m] = witness

    return SearchResult(
        n=n,
        costs=costs,
        witnesses=witnesses,
        completed_layers=completed_layers,
        states_per_layer=states_per_layer,
        visited_states=len(parent),
        expanded_nodes=expanded,
        truncated=truncated,
        truncation_reason=reason,
        caps=caps,
    )


# ---------------------------------------------------------------------------
# Unpruned syntactic enumeration (independent oracle for differential tests)
# ---------------------------------------------------------------------------

def syntactic_min_costs(n: int = 2, max_gates: int = 3):
    """Exact minima up to ``max_gates`` by brute-force syntactic circuits.

    Enumerates every topologically ordered gate sequence: gate k picks an
    ORDERED pair of earlier signals (inputs first), repetition allowed.
    Nothing is pruned - duplicate functional signals are kept - so this
    is an oracle independent of the state-set BFS.  The cost of a
    function is the shortest sequence whose signal set contains it
    (output = any input or gate, matching the lab model).

    Returns (costs, counts) where costs maps mask -> min gates or None,
    and counts maps sequence length -> number of sequences enumerated.
    """
    check_n(n)
    if type(max_gates) is not int or max_gates < 0:
        raise ValueError("max_gates must be a nonnegative integer")
    inputs = input_masks(n)
    full = full_mask(n)
    universe = 1 << (1 << n)
    costs: dict[int, int | None] = {m: None for m in range(universe)}
    counts: dict[int, int] = {}

    def rec(signals: list[int], gates_left_depth: int):
        depth = len(signals) - n
        counts[depth] = counts.get(depth, 0) + 1
        for m in signals:
            if costs[m] is None or depth < costs[m]:
                costs[m] = depth
        if gates_left_depth == 0:
            return
        k = len(signals)
        for (i, j) in itertools.product(range(k), repeat=2):
            signals.append(full ^ (signals[i] & signals[j]))
            rec(signals, gates_left_depth - 1)
            signals.pop()

    rec(list(inputs), max_gates)
    return costs, counts


# ---------------------------------------------------------------------------
# CLI: JSON results (real witnesses, completed layers, model assumptions)
# ---------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description="Exact finite NAND circuit lab")
    p.add_argument("--n", type=int, default=2, choices=[1, 2, 3])
    p.add_argument("--max-gates", type=int, default=None)
    p.add_argument("--max-states", type=int, default=None)
    p.add_argument("--max-states-per-layer", type=int, default=None)
    p.add_argument("--max-nodes", type=int, default=None)
    p.add_argument("--timeout", type=float, default=None,
                   help="wall-time timeout in seconds")
    args = p.parse_args(argv)
    result = search(
        args.n,
        max_gates=args.max_gates,
        max_states=args.max_states,
        max_states_per_layer=args.max_states_per_layer,
        max_nodes=args.max_nodes,
        timeout_seconds=args.timeout,
    )
    print(json.dumps(result.to_dict(), indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
