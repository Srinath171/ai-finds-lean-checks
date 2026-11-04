"""Sample-interpolation obstruction: explicit NAND interpolation.

Claim (elementary, known; no novelty and no P-vs-NP assertion)
----------------------------------------------------------------
For every ``n >= 1`` and every consistently labelled set of ``m``
``n``-bit samples there is an ordered binary NAND circuit, in exactly
the model below, that agrees with every sample label and uses at most

    B(n, m) = 3 + n + (2*n + 1) * m

gates.

Model
-----
* Inputs are the variables ``x0 .. x(n-1)`` only.
* No free constants and no free complemented inputs: the only starting
  signals are the ``n`` inputs themselves.  Negations used by the
  construction are built explicitly with ``NAND(s, s)`` gates.
* The only gate is binary NAND.  Fan-in is exactly two, ordered pairs
  are distinct, and repetition is allowed (``NAND(s, s) = NOT s``).
* Fanout is unlimited: any earlier signal may feed any later gate
  (DAG sharing).  Circuits are topological gate lists.
* The output may be any input or any computed signal.  Size is the
  number of NAND gates.

Construction (the one proved in ``SAMPLE_INTERPOLATION.md``)
-------------------------------------------------------------
1. Precompute the ``n`` negations ``NAND(xi, xi)`` (``n`` gates).
   Signals ``0..n-1`` are the inputs; signal ``n+i`` is ``NOT xi``.
2. For each distinct positively labelled assignment, build its full
   ``n``-literal minterm.  A binary AND of two available signals is
   ``NAND(a, b)`` followed by ``NAND(t, t)``, so a conjunction of
   ``n`` literals costs ``2*(n-1)`` gates (``0`` when ``n == 1``).
3. OR the ``p`` positive minterms.  A binary OR is
   ``NAND(NOT a, NOT b)`` with each NOT built by ``NAND(s, s)``, so
   OR-ing costs ``3*(p-1)`` gates when ``p >= 1`` and ``0`` when
   ``p == 1`` (the single minterm is the output).
4. If ``p == 0`` (no positive sample, including ``m == 0``), use the
   three-gate constant-zero circuit on input ``x0``:
   ``u = NAND(x0, x0)``, ``v = NAND(u, x0)``, ``z = NAND(v, v)``.

Counting for ``p >= 1`` gives ``n + 2*p*(n-1) + 3*(p-1)``
``= n - 3 + p*(2*n + 1) <= 3 + n + (2*n + 1) * m`` because the number
``p`` of distinct positive assignments is at most ``m``.  The
``p == 0`` circuit has ``3 <= B(n, m)`` gates.

A full minterm is true on exactly its own assignment, so the DNF is
true exactly on the positive sample assignments.  Consistency (no
assignment carrying both labels) therefore makes the circuit agree
with every sample.  Duplicate consistent samples are accepted;
contradictory samples are rejected.

Consequence, stated precisely: polynomially many labelled examples
can always be matched by a polynomial-size circuit, so a certificate
whose only content is agreement on such a sample set cannot
distinguish any target from *all* circuits in a superpolynomial size
bound, once that bound exceeds ``B(n, m)``.  This rules out only the
literal sample-only distinguishing-set format.  It does not rule out
arbitrary succinct certificates or other verifiers, and it does not
solve P versus NP.

This module is Python standard library only.  The Boolean evaluator,
the well-formedness checker, the sample-DNF comparison, and the cost
checker below are written independently of the builder's internal
bookkeeping, so tests cross-check the builder rather than restating
it.  Resource caps keep every entry point bounded.
"""

from __future__ import annotations

from dataclasses import dataclass

# ---------------------------------------------------------------------------
# Resource caps (every public entry point is bounded)
# ---------------------------------------------------------------------------

#: Maximum input count.  The construction is polynomial, but sample and
#: truth-table work must stay finite and reviewable in this lab.
MAX_N = 16
#: Maximum number of sample entries (duplicates included).
MAX_SAMPLES = 4096
#: Maximum number of assignments enumerated by a full truth-table call
#: (``2**12 = 4096``).  Building or evaluating on samples only is not
#: subject to this cap; enumerating the whole cube is.
MAX_TRUTH_ASSIGNMENTS = 4096
#: Maximum gate count accepted by the evaluator / checkers. The loose
#: proved bound is ``3 + 16 + 33 * 4096 = 135187``; the actual largest
#: construction emits 135181 gates, below this ceiling.
MAX_GATES = 200_000
#: Bulk simulation budget: one unit per checked gate and per input/gate
#: visited at each distinct query point. Checked before any simulation.
MAX_CHECK_WORK = 2_000_000

MODEL_ASSUMPTIONS = [
    "inputs are the variables x0..x(n-1) only",
    "no free constants: 0 and 1 are not available unless built by gates",
    "no free complemented inputs: NOT xi is not available unless built",
    "only gate is binary NAND; fan-in exactly two; ordered pairs; repetition allowed (NAND(s,s) = NOT s)",
    "unlimited fanout: computed signals may be reused by any later gates (DAG sharing)",
    "output may be any input or computed signal; size = number of NAND gates",
    "an assignment is a tuple of Bool of length n; index i of the tuple is xi",
]

SCOPE_NOTE = (
    "Elementary interpolation bound B(n,m) = 3 + n + (2*n + 1)*m for "
    "consistently labelled samples. It rules out only the literal "
    "sample-only distinguishing-set format; it does not rule out "
    "arbitrary succinct certificates and does not solve P vs NP."
)


# ---------------------------------------------------------------------------
# Strict validation helpers (bool is never an int in this module)
# ---------------------------------------------------------------------------

def _is_int(x) -> bool:
    return type(x) is int


def _is_bool(x) -> bool:
    return type(x) is bool


def _validate_n(n) -> int:
    if not _is_int(n):
        raise ValueError("n must be a strict int (bool is not an int)")
    if not 1 <= n <= MAX_N:
        raise ValueError("n must satisfy 1 <= n <= %d" % MAX_N)
    return n


def _validate_m(m) -> int:
    if not _is_int(m):
        raise ValueError("m must be a strict int (bool is not an int)")
    if not 0 <= m <= MAX_SAMPLES:
        raise ValueError("m must satisfy 0 <= m <= %d" % MAX_SAMPLES)
    return m


def gate_bound(n, m) -> int:
    """Exact cost bound ``B(n, m) = 3 + n + (2*n + 1) * m``.

    Strict: ``n`` and ``m`` must be genuine ``int`` (never ``bool``),
    ``n >= 1``, ``m >= 0``, both within the module resource caps.
    """
    _validate_n(n)
    _validate_m(m)
    return 3 + n + (2 * n + 1) * m


# Backwards-friendly / descriptive aliases for the same exact bound.
cost_bound = gate_bound
interpolation_bound = gate_bound


def _validate_assignment(n, assignment, what="assignment"):
    if isinstance(assignment, (str, bytes)) or not isinstance(assignment, (list, tuple)):
        raise ValueError("%s must be a list/tuple of Bool" % what)
    if len(assignment) != n:
        raise ValueError("%s must have length n=%d" % (what, n))
    for v in assignment:
        if not _is_bool(v):
            raise ValueError("%s entries must be Bool (bool only, no int)" % what)
    return tuple(assignment)


def validate_samples(n, samples):
    """Validate and normalise ``samples``; reject contradictions.

    ``samples`` must be a list/tuple of ``(assignment, label)`` pairs,
    each assignment a list/tuple of exactly ``n`` Bool values and each
    label a Bool.  Duplicate assignments with the same label are kept
    (they count toward ``m``).  The same assignment with two different
    labels raises ``ValueError``.  Returns a tuple of
    ``(assignment_tuple, label)`` pairs in input order.
    """
    _validate_n(n)
    if isinstance(samples, (str, bytes)) or not isinstance(samples, (list, tuple)):
        raise ValueError("samples must be a list/tuple of (assignment, label) pairs")
    if len(samples) > MAX_SAMPLES:
        raise ValueError("sample count exceeds cap %d" % MAX_SAMPLES)
    normalised = []
    seen = {}
    for entry in samples:
        if isinstance(entry, (str, bytes)) or not isinstance(entry, (list, tuple)):
            raise ValueError("each sample must be a (assignment, label) pair")
        if len(entry) != 2:
            raise ValueError("each sample must have exactly two components")
        assignment_raw, label = entry
        assignment = _validate_assignment(n, assignment_raw, "sample assignment")
        if not _is_bool(label):
            raise ValueError("sample labels must be Bool")
        if assignment in seen and seen[assignment] is not label:
            raise ValueError("contradictory labels for assignment %r" % (assignment,))
        seen[assignment] = label
        normalised.append((assignment, label))
    return tuple(normalised)


def positive_assignments(normalised_samples):
    """Distinct positively labelled assignments, first-appearance order.

    ``normalised_samples`` is the output of :func:`validate_samples`.
    Duplicates collapse to one entry, which only lowers the gate count
    relative to the bound stated with ``m = len(samples)``.
    """
    if not isinstance(normalised_samples, (list, tuple)):
        raise ValueError("normalised samples must be a bounded list/tuple")
    if len(normalised_samples) > MAX_SAMPLES:
        raise ValueError("sample count exceeds cap")
    if not normalised_samples:
        return ()
    first = normalised_samples[0]
    if (not isinstance(first, (list, tuple)) or len(first) != 2
            or not isinstance(first[0], (list, tuple))):
        raise ValueError("malformed normalised sample")
    checked = validate_samples(len(first[0]), normalised_samples)
    out = []
    seen = set()
    for assignment, label in checked:
        if label and assignment not in seen:
            seen.add(assignment)
            out.append(assignment)
    return tuple(out)


# ---------------------------------------------------------------------------
# Circuit representation
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Circuit:
    """An ordered NAND circuit.

    Signals ``0..n-1`` are the inputs ``x0..x(n-1)``.  Signal ``n+k``
    is the output of ``gates[k]``.  Gate ``k`` is a pair ``(i, j)`` of
    earlier signal indices (``i, j < n + k``; ``i == j`` allowed)
    meaning ``NAND(signal_i, signal_j)``.  ``output`` is the index of
    the signal taken as the circuit output.
    """

    n: int
    gates: tuple
    output: int

    @property
    def size(self) -> int:
        return len(self.gates)

    def to_dict(self) -> dict:
        return {
            "n": self.n,
            "gates": [[i, j] for (i, j) in self.gates],
            "output": self.output,
            "size": self.size,
        }


# Descriptive aliases: one representation, several discoverable names.
InterpolatingCircuit = Circuit
NANDCircuit = Circuit


# ---------------------------------------------------------------------------
# Builder
# ---------------------------------------------------------------------------

def build_interpolating_circuit(n, samples) -> Circuit:
    """Build a NAND circuit matching every consistently labelled sample.

    Implements exactly the construction in the module docstring.
    Raises ``ValueError`` on malformed input, contradictory labels, or
    any resource-cap violation.  The returned circuit is well-formed
    (see :func:`is_wellformed_circuit`) and its size is at most
    ``gate_bound(n, len(samples))`` (see :func:`check_cost_bound`).
    Unused precomputed signals may appear; the model permits them.
    """
    normalised = validate_samples(n, samples)
    m = len(normalised)
    # Refuse before building if even the proved bound exceeds the cap.
    if gate_bound(n, m) > MAX_GATES:
        raise ValueError("interpolating circuit would exceed gate cap")
    positives = positive_assignments(normalised)

    if not positives:
        # Three-gate constant zero from input x0:
        #   u = NAND(x0, x0) = NOT x0        (signal n)
        #   v = NAND(u, x0)  = NOT(NOT x0 AND x0) = 1   (signal n+1)
        #   z = NAND(v, v)   = NOT 1 = 0     (signal n+2, output)
        gates = ((0, 0), (n, 0), (n + 1, n + 1))
        return Circuit(n=n, gates=gates, output=n + 2)

    gates = []

    def next_signal() -> int:
        return n + len(gates)

    # Phase 1: the n negations.  Signal n+i becomes NOT xi.
    for i in range(n):
        gates.append((i, i))

    def literal_signal(i: int, bit: bool) -> int:
        # xi itself is signal i; NOT xi is the precomputed signal n+i.
        # No complemented input is ever used for free.
        return i if bit else n + i

    # Phase 2: one full minterm per distinct positive assignment.
    minterm_signals = []
    for assignment in positives:
        literals = [literal_signal(i, assignment[i]) for i in range(n)]
        if n == 1:
            minterm_signals.append(literals[0])
            continue
        current = literals[0]
        for k in range(1, n):
            t = next_signal()
            gates.append((current, literals[k]))  # NAND(current, lit)
            gates.append((t, t))                  # NOT of that = AND
            current = t + 1
        minterm_signals.append(current)

    # Phase 3: OR the minterms, 3 gates per binary OR.
    if len(minterm_signals) == 1:
        output = minterm_signals[0]
    else:
        current = minterm_signals[0]
        for nxt in minterm_signals[1:]:
            na = next_signal()
            gates.append((current, current))  # NOT current
            nb = na + 1
            gates.append((nxt, nxt))          # NOT nxt
            gates.append((na, nb))            # NAND(NOT, NOT) = OR
            current = nb + 1
        output = current

    return Circuit(n=n, gates=tuple(gates), output=output)


# Aliases over the one shared implementation.
build_circuit = build_interpolating_circuit
build_interpolation_circuit = build_interpolating_circuit
interpolate_samples = build_interpolating_circuit


# ---------------------------------------------------------------------------
# Independent Boolean evaluator (no builder bookkeeping, no masks)
# ---------------------------------------------------------------------------

def evaluate_circuit(circuit, assignment) -> bool:
    """Evaluate ``circuit`` on one assignment by Boolean simulation.

    Written directly from the gate semantics: start from the assignment
    bits, append ``not (a and b)`` per gate in order, return the output
    signal.  Raises ``ValueError`` on any malformed circuit, gate index,
    or assignment.  This evaluator shares no code with the builder.
    """
    n, gates, output = _checked_circuit_parts(circuit)
    values_in = _validate_assignment(n, assignment)
    _check_evaluation_work(n, gates, 1)
    return _evaluate_checked(gates, output, values_in)


def _evaluate_checked(gates, output, assignment):
    """Boolean semantics on already validated, immutable circuit parts."""
    signals = list(assignment)
    for i, j in gates:
        signals.append(not (signals[i] and signals[j]))
    return signals[output]


def _check_evaluation_work(n, gates, num_points):
    """Refuse oversized bulk work before entering any simulation loop."""
    work = len(gates) + num_points * (n + len(gates))
    if work > MAX_CHECK_WORK:
        raise ValueError("evaluation work exceeds cap %d" % MAX_CHECK_WORK)


def _matches_checked_samples(n, gates, output, normalised):
    # Validation already established consistency, so duplicates add no query.
    points = dict(normalised)
    _check_evaluation_work(n, gates, len(points))
    return all(_evaluate_checked(gates, output, a) is label
               for a, label in points.items())


# Aliases over the one shared evaluator.
evaluate_bool = evaluate_circuit
eval_circuit = evaluate_circuit
evaluate_on_assignment = evaluate_circuit


def _checked_circuit_parts(circuit):
    """Strictly extract ``(n, gates, output)`` or raise ``ValueError``."""
    if not isinstance(circuit, Circuit):
        raise ValueError("circuit must be a Circuit")
    n = circuit.n
    _validate_n(n)
    gates_raw = circuit.gates
    if isinstance(gates_raw, (str, bytes)) or not isinstance(gates_raw, (list, tuple)):
        raise ValueError("circuit gates must be a list/tuple of pairs")
    if len(gates_raw) > MAX_GATES:
        raise ValueError("circuit exceeds gate cap")
    gates = []
    for k, gate in enumerate(gates_raw):
        if isinstance(gate, (str, bytes)) or not isinstance(gate, (list, tuple)):
            raise ValueError("gate %d must be a pair" % k)
        if len(gate) != 2:
            raise ValueError("gate %d must have exactly two fan-ins" % k)
        i, j = gate
        if not _is_int(i) or not _is_int(j):
            raise ValueError("gate %d fan-ins must be strict ints" % k)
        if not (0 <= i < n + k and 0 <= j < n + k):
            raise ValueError("gate %d references a not-yet-built signal" % k)
        gates.append((i, j))
    output = circuit.output
    if not _is_int(output):
        raise ValueError("circuit output must be a strict int")
    if not 0 <= output < n + len(gates):
        raise ValueError("circuit output references a nonexistent signal")
    return n, tuple(gates), output


# ---------------------------------------------------------------------------
# Gate-index well-formedness checker
# ---------------------------------------------------------------------------

def is_wellformed_circuit(circuit) -> bool:
    """True iff ``circuit`` is a well-formed ordered NAND circuit.

    Checks, with strict integer typing throughout: ``n`` in range,
    every gate ``k`` has two strict-int fan-ins in ``[0, n+k)`` (so no
    gate can reference itself, a later gate, a free constant, or a free
    complemented input), the output is a strict int in
    ``[0, n + size)``, and the gate count is within the cap.  Returns
    ``False`` (never raises) on any malformed value.
    """
    try:
        _checked_circuit_parts(circuit)
        return True
    except Exception:
        return False


def check_wellformed(circuit) -> bool:
    """Like :func:`is_wellformed_circuit` but raises ``ValueError``."""
    _checked_circuit_parts(circuit)
    return True


# Aliases.
validate_circuit = check_wellformed
is_wellformed = is_wellformed_circuit


# ---------------------------------------------------------------------------
# Sample DNF, independently of any gate (direct assignment equality)
# ---------------------------------------------------------------------------

def dnf_value(assignment, positives) -> bool:
    """Sample-DNF value: True iff ``assignment`` equals a positive.

    ``positives`` is an iterable of assignment tuples.  This is the
    independent semantic reference for the construction: a full
    minterm is true on exactly its own assignment, and the OR of the
    minterms is therefore true exactly on the positive assignments.
    No gate is simulated here.
    """
    if not isinstance(assignment, (list, tuple)):
        raise ValueError("assignment must be a list/tuple of Bool")
    n = _validate_n(len(assignment))
    target = _validate_assignment(n, assignment)
    if not isinstance(positives, (list, tuple)) or len(positives) > MAX_SAMPLES:
        raise ValueError("positives must be a bounded list/tuple")
    checked = {_validate_assignment(n, pos, "positive assignment") for pos in positives}
    return target in checked


def sample_dnf_value(n, samples, assignment) -> bool:
    """DNF value of the sample set at ``assignment`` (validated)."""
    normalised = validate_samples(n, samples)
    point = _validate_assignment(n, assignment)
    return dnf_value(point, positive_assignments(normalised))


# Aliases.
dnf_predict = sample_dnf_value
matches_sample_dnf = sample_dnf_value


# ---------------------------------------------------------------------------
# Cost-bound and full interpolation checkers
# ---------------------------------------------------------------------------

def check_cost_bound(n, m, circuit) -> bool:
    """True iff ``circuit`` is a Circuit on ``n`` inputs with
    ``size <= B(n, m)``.  False on any malformed value; never raises."""
    try:
        bound = gate_bound(n, m)
        circuit_n, gates, _output = _checked_circuit_parts(circuit)
        return circuit_n == n and len(gates) <= bound
    except Exception:
        return False


# Aliases.
verify_cost_bound = check_cost_bound
cost_bound_ok = check_cost_bound


def circuit_matches_samples(n, samples, circuit) -> bool:
    """True iff the (well-formed) circuit agrees with every sample.

    Each sample is checked with the independent Boolean evaluator
    against its label.  False on malformed input or work-cap refusal; never raises.
    """
    try:
        normalised = validate_samples(n, samples)
        circuit_n, gates, output = _checked_circuit_parts(circuit)
        if circuit_n != n:
            return False
        return _matches_checked_samples(n, gates, output, normalised)
    except Exception:
        return False


def verify_interpolation(n, samples, circuit) -> bool:
    """Full checker: well-formed, matches every sample, within bound.

    The bound uses ``m = len(samples)`` (duplicates included), exactly
    as in ``B(n, m) = 3 + n + (2*n + 1) * m``.  False on any malformed
    or non-matching value, or work-cap refusal; never raises.
    """
    try:
        normalised = validate_samples(n, samples)
        circuit_n, gates, output = _checked_circuit_parts(circuit)
        if circuit_n != n or len(gates) > gate_bound(n, len(normalised)):
            return False
        return _matches_checked_samples(n, gates, output, normalised)
    except Exception:
        return False


# Aliases.
verify_interpolating_circuit = verify_interpolation
verify_circuit = verify_interpolation


# ---------------------------------------------------------------------------
# Full truth-table comparison: circuit versus sample DNF on the whole cube
# ---------------------------------------------------------------------------

def _all_assignments(n):
    """All ``2**n`` assignments in index order: bit ``i`` of ``a`` is ``xi``."""
    return [
        tuple(bool((a >> i) & 1) for i in range(n))
        for a in range(1 << n)
    ]


def circuit_truth_table(n, circuit):
    """Tuple of circuit outputs over all assignments, in index order.

    Refuses (``ValueError``) when ``2**n`` exceeds the truth-table cap,
    and also refuses when the aggregate evaluation work exceeds
    ``MAX_CHECK_WORK``. Validation happens once, before simulation.
    """
    _validate_n(n)
    if (1 << n) > MAX_TRUTH_ASSIGNMENTS:
        raise ValueError("truth-table enumeration exceeds assignment cap")
    circuit_n, gates, output = _checked_circuit_parts(circuit)
    if circuit_n != n:
        raise ValueError("circuit is not well-formed for this n")
    _check_evaluation_work(n, gates, 1 << n)
    return tuple(_evaluate_checked(gates, output, a) for a in _all_assignments(n))


def dnf_truth_table(n, samples):
    """Tuple of sample-DNF outputs over all assignments, in index order."""
    _validate_n(n)
    if (1 << n) > MAX_TRUTH_ASSIGNMENTS:
        raise ValueError("truth-table enumeration exceeds assignment cap")
    normalised = validate_samples(n, samples)
    positives = set(positive_assignments(normalised))
    return tuple(a in positives for a in _all_assignments(n))


def compare_circuit_to_dnf_on_all_assignments(n, samples, circuit) -> bool:
    """True iff circuit and sample DNF agree on the *whole* cube.

    Stronger than agreement on the samples alone: the construction
    computes the sample DNF as a Boolean function, so the two truth
    tables must be identical. Returns False on disagreement, malformed
    input, or an assignment/aggregate-work cap refusal. A False result
    alone therefore does not establish a mathematical counterexample.
    """
    try:
        return circuit_truth_table(n, circuit) == dnf_truth_table(n, samples)
    except Exception:
        return False
