"""Exact n=2 finite graph-support experiment; no asymptotic claim.

Coordinates are (x0,x1,z), with graph z=NAND(x0,x1) and graph XOR mask6.
Search states are sets of four-row graph truth masks. A gate that duplicates
an available graph function can be removed/replaced by the earlier signal:
graph labels remain unchanged, although the off-graph extension can change.
The latter is allowed here because the task minimizes over all extensions.
Breadth-first distances therefore give minimum graph-fitting NAND gatecounts.

Every discovered minimum has an original-index M=3 witness. A separate Boolean
simulator evaluates all8 assignments, graph fitting, and semantic dependencies.
Caps yield CAPPED, never NO_CIRCUIT or an exact minimum. Only n=2 is supported.
Report source_sha256_lf hashes source bytes after CRLF->LF, then CR->LF;
all other bytes are unchanged, so Git checkout line endings do not affect it.
"""
from __future__ import annotations
import argparse
from collections import deque
import hashlib
import itertools
import json
from pathlib import Path

N = 2
M = 3
GRAPH_MASKS = (10, 12, 7)
XOR = 6
MAX_STATES = 65536
MAX_GATES = 16
MAX_TRANSITIONS = 2_000_000
RESULT_PATH = Path(__file__).resolve().parent / 'results' / 'support-holes-n2.json'
SCOPE = 'Exact finite n=2 experiment only; no asymptotic lower bound or P-versus-NP conclusion.'
SOURCE_HASH_NORMALIZATION = 'CRLF->LF, then CR->LF; all other bytes unchanged'


def _source_sha256_lf():
    source = Path(__file__).read_bytes().replace(b'\r\n', b'\n').replace(b'\r', b'\n')
    return hashlib.sha256(source).hexdigest()


def _support(support, n=2):
    if type(n) is not int or n != N:
        raise ValueError('n_must_be_exactly_2')
    if type(support) not in (list, tuple) or not 1 <= len(support) <= M:
        raise ValueError('support_requires_nonempty_coordinate_sequence')
    if any(type(i) is not int or not 0 <= i < M for i in support) or len(set(support)) != len(support):
        raise ValueError('invalid_support_coordinate')
    return tuple(sorted(support))


def _target(target):
    if type(target) is not int or not 0 <= target < 16:
        raise ValueError('target_must_be_4row_mask')
    return target


def graph_rows(n=2):
    _support([0], n)
    return [[a & 1, (a >> 1) & 1, int(not ((a & 1) and ((a >> 1) & 1)))] for a in range(4)]


def project_labels(support, target_mask=XOR, *, n=2):
    support = _support(support, n)
    _target(target_mask)
    buckets = {}
    for a, row in enumerate(graph_rows(n)):
        pattern = sum(row[coordinate] << position for position, coordinate in enumerate(support))
        buckets.setdefault(pattern, []).append((a, (target_mask >> a) & 1))
    entries, conflicts = [], []
    for pattern, rows in sorted(buckets.items()):
        labels = sorted({label for _, label in rows})
        entries.append({'pattern': pattern, 'bits': [(pattern >> i) & 1 for i in range(len(support))],
                        'graph_rows': [a for a, _ in rows], 'labels': labels})
        if len(labels) > 1:
            first = rows[0]
            opposite = next(row for row in rows if row[1] != first[1])
            conflicts.append({'pattern': pattern, 'rows': [first[0], opposite[0]],
                              'labels': [first[1], opposite[1]]})
    holes = [a for a in range(1 << len(support)) if a not in buckets]
    return {'support': list(support), 'status': 'INCONSISTENT' if conflicts else 'CONSISTENT',
            'image_size': len(buckets), 'hole_count': len(holes), 'holes': holes,
            'projected_labels': entries, 'conflicts': conflicts}


def verify_witness(witness, support, target_mask=XOR, *, n=2):
    """Independent full Boolean simulation, without graph-mask NAND arithmetic."""
    try:
        support = _support(support, n)
        _target(target_mask)
        if type(witness) is not dict or set(witness) != {'gates', 'output'}:
            raise ValueError('invalid_witness_shape')
        gates, output = witness['gates'], witness['output']
        if type(gates) not in (list, tuple) or len(gates) > MAX_GATES:
            raise ValueError('invalid_gate_list')
        used = set()
        for index, gate in enumerate(gates):
            if (type(gate) not in (list, tuple) or len(gate) != 2
                    or any(type(wire) is not int or not 0 <= wire < M + index for wire in gate)):
                raise ValueError('non_topological_gate')
            used.update(wire for wire in gate if wire < M)
        if type(output) is not int or not 0 <= output < M + len(gates):
            raise ValueError('invalid_output_selector')
        if output < M:
            used.add(output)
        if not used.issubset(support):
            raise ValueError('primary_coordinate_outside_support')
        values = []
        for assignment in range(8):
            signals = [bool((assignment >> i) & 1) for i in range(M)]
            for left, right in gates:
                signals.append(not (signals[left] and signals[right]))
            values.append(int(signals[output]))
        graph_values = []
        for x in range(4):
            x0, x1 = x & 1, (x >> 1) & 1
            z = int(not (bool(x0) and bool(x1)))
            graph_values.append(values[x0 + 2*x1 + 4*z])
        graph_mask = sum(value << a for a, value in enumerate(graph_values))
        dependencies, essential = [], []
        for coordinate in range(M):
            pair = next(((a, a ^ (1 << coordinate)) for a in range(8)
                         if values[a] != values[a ^ (1 << coordinate)]), None)
            if pair is not None:
                dependencies.append(coordinate)
                essential.append({'coordinate': coordinate, 'assignments': list(pair),
                                  'values': [values[pair[0]], values[pair[1]]]})
        reachable, pending, syntactic_dependencies = set(), [output], set()
        while pending:
            wire = pending.pop()
            if wire in reachable:
                continue
            reachable.add(wire)
            if wire < M:
                syntactic_dependencies.add(wire)
            else:
                pending.extend(gates[wire-M])
        return {'valid': graph_mask == target_mask and set(dependencies).issubset(support),
                'reason': None if graph_mask == target_mask else 'graph_label_mismatch',
                'full_extension_mask': sum(value << a for a, value in enumerate(values)),
                'full_extension_values': values, 'graph_mask': graph_mask,
                'syntactic_support': sorted(used), 'dependency_support': sorted(syntactic_dependencies),
                'semantic_support': dependencies, 'essential_witnesses': essential}
    except (ValueError, TypeError, IndexError, KeyError) as exc:
        return {'valid': False, 'reason': str(exc)}


def _reconstruct(state, target, parents, support):
    path = []
    while parents[state] is not None:
        previous, left, right, value = parents[state]
        path.append((left, right, value))
        state = previous
    signals = {GRAPH_MASKS[coordinate]: coordinate for coordinate in support}
    gates = []
    for left, right, value in reversed(path):
        gates.append([signals[left], signals[right]])
        signals[value] = M + len(gates) - 1
    return {'gates': gates, 'output': signals[target]}


def search_support(support, target_mask=XOR, *, n=2, max_states=MAX_STATES,
                   max_gates=MAX_GATES, max_transitions=MAX_TRANSITIONS):
    """Exhaust all reachable semantic sets; only a complete run reports exactness."""
    try:
        support = _support(support, n)
        if target_mask is not None:
            _target(target_mask)
        for value, low, high in ((max_states, 1, MAX_STATES), (max_gates, 0, MAX_GATES),
                                 (max_transitions, 1, MAX_TRANSITIONS)):
            if type(value) is not int or not low <= value <= high:
                raise ValueError('invalid_search_limit')
    except ValueError as exc:
        return {'status': 'MALFORMED', 'exact': False, 'min_gates': None, 'witness': None, 'reason': str(exc)}
    start = sum(1 << GRAPH_MASKS[coordinate] for coordinate in support)
    parents, depths = {start: None}, {start: 0}
    first = {GRAPH_MASKS[coordinate]: (0, start) for coordinate in support}
    queue = deque([start])
    transitions = 0
    layer_sizes = [1]
    gate_limited = False

    def capped(reason):
        return {'status': 'CAPPED', 'exact': False, 'exhaustive': False, 'reason': reason,
                'min_gates': None, 'witness': None, 'functions': None,
                'visited_states': len(parents), 'transitions': transitions, 'states_by_depth': layer_sizes}

    while queue:
        state = queue.popleft()
        depth = depths[state]
        available = [mask for mask in range(16) if (state >> mask) & 1]
        for position, left in enumerate(available):
            # NAND is commutative, so this covers every ordered pair semantically.
            for right in available[position:]:
                if transitions >= max_transitions:
                    return capped('transition_limit')
                transitions += 1
                value = 15 ^ (left & right)
                if (state >> value) & 1:
                    continue  # Repeated graph functions cannot improve a minimum.
                following = state | (1 << value)
                if following in parents:
                    continue
                if depth >= max_gates:
                    gate_limited = True
                    continue
                if len(parents) >= max_states:
                    return capped('state_limit')
                parents[following] = (state, left, right, value)
                depths[following] = depth + 1
                queue.append(following)
                if len(layer_sizes) <= depth + 1:
                    layer_sizes.append(0)
                layer_sizes[depth+1] += 1
                first.setdefault(value, (depth+1, following))
    if gate_limited:
        return capped('gate_limit')

    def certified(mask):
        if mask not in first:
            return {'mask': mask, 'status': 'NO_CIRCUIT', 'exact': True, 'min_gates': None, 'witness': None}
        cost, state = first[mask]
        witness = _reconstruct(state, mask, parents, support)
        verification = verify_witness(witness, support, mask, n=n)
        if not verification['valid'] or len(witness['gates']) != cost:
            raise RuntimeError('independent_witness_check_failed')
        return {'mask': mask, 'status': 'FOUND_EXACT', 'exact': True,
                'min_gates': cost, 'witness': witness, 'verification': verification}

    result = {'status': 'EXHAUSTIVE_MINIMA', 'exact': True, 'exhaustive': True, 'reason': None,
              'visited_states': len(parents), 'transitions': transitions, 'states_by_depth': layer_sizes}
    if target_mask is None:
        result['functions'] = [certified(mask) for mask in range(16)]
    else:
        result.update(certified(target_mask))
    return result


def experiment(*, n=2, max_states=MAX_STATES, max_gates=MAX_GATES, max_transitions=MAX_TRANSITIONS):
    _support([0], n)
    limits = dict(max_states=max_states, max_gates=max_gates, max_transitions=max_transitions)
    cases = []
    for size in range(1, M+1):
        for support in itertools.combinations(range(M), size):
            projection = project_labels(support, n=n)
            circuit = search_support(support, n=n, **limits)
            if projection['status'] == 'INCONSISTENT' and circuit['status'] == 'FOUND_EXACT':
                raise RuntimeError('projection_and_search_disagree')
            cases.append({'support': list(support), 'projection': projection, 'circuit': circuit})
    ordinary = search_support([0,1], None, n=n, **limits)
    consistent = [case for case in cases if case['projection']['status'] == 'CONSISTENT']
    return {'format': 'support-holes-n2-v2', 'source_sha256_lf': _source_sha256_lf(),
            'source_hash_normalization': SOURCE_HASH_NORMALIZATION,
            'scope': SCOPE, 'n': n, 'M': M, 'graph_rows': graph_rows(n), 'target_mask': XOR,
            'target_values': [0,1,1,0], 'limits': limits,
            'model': {'gate': 'binary NAND; repetition and sharing allowed; no free constants or complements',
                      'witness_indices': 'original primary indices0,1,2; gate i has signal index3+i',
                      'assignment_order': 'bit i of assignment is coordinate i; bit a of a mask is output on assignment a',
                      'search': 'complete BFS over sets of graph-restricted four-row masks; no claim about a fixed off-graph extension'},
            'cases': cases, 'ordinary_two_input_all_masks': ordinary,
            'summary': {'consistent_supports': [case['support'] for case in consistent],
                        'consistent_holes_and_costs': [{'support': case['support'],
                            'holes': case['projection']['hole_count'], 'min_gates': case['circuit'].get('min_gates'),
                            'status': case['circuit']['status']} for case in consistent]}}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true', help='Write the fixed project result path')
    args = parser.parse_args(argv)
    result = experiment()
    if args.write:
        RESULT_PATH.parent.mkdir(parents=True, exist_ok=True)
        RESULT_PATH.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({'summary':result['summary'],'source_sha256_lf':result['source_sha256_lf'],
                      'result_path':str(RESULT_PATH) if args.write else None},indent=2))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
