"""Complete small NAND catalogue for C(f)=2 and a primary-input NAND g."""
from collections import Counter, defaultdict
import hashlib
import itertools
import json
from pathlib import Path

MAX_GATE_LISTS = 1000
MAX_ORBIT_WORK = 200000


def _int(value, low, high):
    return type(value) is int and low <= value <= high


def primary_masks(n):
    if not _int(n, 1, 5): raise ValueError('n must be an exact integer 1..5')
    return [sum(1 << a for a in range(1 << n) if (a >> i) & 1) for i in range(n)]


def verify_witness(n, targets, witness, cost=None):
    """Independent Boolean simulation, using no NAND truth-mask operations."""
    if not _int(n, 1, 5) or type(targets) is not list or not 1 <= len(targets) <= 2:
        return False
    if any(not _int(t, 0, (1 << (1 << n)) - 1) for t in targets): return False
    if type(witness) is not dict or set(witness) != {'gates', 'outputs'}: return False
    gates, outputs = witness['gates'], witness['outputs']
    if type(gates) is not list or len(gates) > 3 or type(outputs) is not list or len(outputs) != len(targets): return False
    if cost is not None and (not _int(cost, 0, 3) or len(gates) != cost): return False
    for k, pair in enumerate(gates):
        if type(pair) is not list or len(pair) != 2 or any(not _int(i, 0, n + k - 1) for i in pair): return False
    if any(not _int(i, 0, n + len(gates) - 1) for i in outputs): return False
    observed = [0] * len(outputs)
    for assignment in range(1 << n):
        values = [bool((assignment >> i) & 1) for i in range(n)]
        for left, right in gates: values.append(not (values[left] and values[right]))
        for i, output in enumerate(outputs):
            if values[output]: observed[i] += 1 << assignment
    return observed == targets


def formula_masks(n):
    """Four independently evaluated Boolean families; parameter order is explicit."""
    primary_masks(n)
    result = {}
    def add(family, parameters, predicate):
        mask = sum(1 << a for a in range(1 << n) if predicate([bool((a >> i) & 1) for i in range(n)]))
        if mask in result: raise AssertionError('formula families overlap')
        result[mask] = {'family': family, 'parameters': list(parameters)}
    add('constant_one', (), lambda x: True)
    for a, b in itertools.combinations(range(n), 2):
        add('and', (a, b), lambda x, a=a, b=b: x[a] and x[b])
    for a, b in itertools.permutations(range(n), 2):
        add('implication', (a, b), lambda x, a=a, b=b: (not x[a]) or x[b])
    for k in range(n):
        for a, b in itertools.combinations([i for i in range(n) if i != k], 2):
            add('not_k_or_ab', (k, a, b), lambda x, k=k, a=a, b=b: (not x[k]) or (x[a] and x[b]))
    return result


def permute_mask(n, mask, permutation):
    primary_masks(n)
    if not _int(mask, 0, (1 << (1 << n)) - 1) or type(permutation) is not tuple or any(type(i) is not int for i in permutation) or sorted(permutation) != list(range(n)):
        raise ValueError('invalid mask or permutation')
    answer = 0
    for assignment in range(1 << n):
        old = sum(((assignment >> permutation[i]) & 1) << i for i in range(n))
        answer |= ((mask >> old) & 1) << assignment
    return answer


def build_catalogue(n=5, *, max_gate_lists=MAX_GATE_LISTS, max_orbit_work=MAX_ORBIT_WORK):
    """Complete syntactic enumeration; cap refusals carry no exact catalogue."""
    if not _int(n, 1, 5): return {'status': 'MALFORMED', 'reason': 'n_must_be_1_to_5'}
    if not _int(max_gate_lists, 0, MAX_GATE_LISTS) or not _int(max_orbit_work, 0, MAX_ORBIT_WORK):
        return {'status': 'MALFORMED', 'reason': 'invalid_cap'}
    primary, full = primary_masks(n), (1 << (1 << n)) - 1
    costs, witnesses, first_options = {}, {}, defaultdict(dict)
    lists_by_size = [0, 0, 0]
    count = 0
    def visit(gates, signals):
        nonlocal count
        if count >= max_gate_lists: return False
        count += 1
        lists_by_size[len(gates)] += 1
        for selector, mask in enumerate(signals):
            if mask not in costs or len(gates) < costs[mask]:
                costs[mask] = len(gates)
                witnesses[mask] = {'gates': [list(g) for g in gates], 'outputs': [selector]}
        if len(gates) == 2:
            first_options[signals[-1]].setdefault(signals[n], {'gates': [list(g) for g in gates], 'outputs': [n + 1, n]})
        if len(gates) < 2:
            for left, right in itertools.product(range(len(signals)), repeat=2):
                value = full ^ (signals[left] & signals[right])
                if not visit(gates + [(left, right)], signals + [value]): return False
        return True
    if not visit([], list(primary)):
        return {'status': 'UNKNOWN', 'reason': 'gate_list_cap', 'gate_lists_visited': count}
    minimal_two = sorted(f for f, c in costs.items() if c == 2)
    forms = formula_masks(n)
    if set(minimal_two) != set(forms): raise AssertionError('enumeration/form classification mismatch')
    g_pairs = {}
    for a, b in itertools.product(range(n), repeat=2):
        g_pairs.setdefault(full ^ (primary[a] & primary[b]), [a, b])
    all_pairs = {}
    for f in minimal_two:
        if not verify_witness(n, [f], witnesses[f], 2): raise AssertionError('single witness rejected')
        for g, gate in sorted(g_pairs.items()):
            if g in first_options[f]:
                joint = first_options[f][g]
                cost, reason = 2, 'complete_two_gate_enumeration_contains_both_outputs'
            else:
                joint = {'gates': witnesses[f]['gates'] + [gate], 'outputs': [witnesses[f]['outputs'][0], n + 2]}
                cost, reason = 3, 'no_two_gate_witness_then_append_one_gate_for_g'
            if not verify_witness(n, [f, g], joint, cost): raise AssertionError('joint witness rejected')
            all_pairs[f, g] = {'f': f, 'g': g, 'single_cost': 2, 'joint_cost': cost,
                              'family': forms[f]['family'], 'parameters': forms[f]['parameters'],
                              'single_witness': witnesses[f], 'joint_witness': joint,
                              'lower_bound_basis': reason}
    permutations = list(itertools.permutations(range(n)))
    required_work = len(all_pairs) * len(permutations)
    if required_work > max_orbit_work:
        return {'status': 'UNKNOWN', 'reason': 'orbit_work_cap', 'gate_lists_visited': count,
                'required_orbit_work': required_work}
    images = {mask: [permute_mask(n, mask, p) for p in permutations]
              for mask in sorted(set(minimal_two) | set(g_pairs))}
    groups = defaultdict(list)
    for pair in all_pairs:
        f, g = pair
        representative = min(zip(images[f], images[g]))
        groups[representative].append(pair)
    catalogue = []
    for representative, members in sorted(groups.items()):
        entry = dict(all_pairs[representative])
        if len({all_pairs[p]['joint_cost'] for p in members}) != 1: raise AssertionError('joint cost not permutation invariant')
        if len({all_pairs[p]['family'] for p in members}) != 1: raise AssertionError('family not permutation invariant')
        entry['orbit_size'] = len(members)
        entry['first_gate_options_for_f'] = sorted(first_options[representative[0]])
        catalogue.append(entry)
    family_summary = {}
    for family in ('constant_one', 'and', 'implication', 'not_k_or_ab'):
        entries = [e for e in all_pairs.values() if e['family'] == family]
        reps = [e for e in catalogue if e['family'] == family]
        family_summary[family] = {'functions': sum(v['family'] == family for v in forms.values()),
                                  'pairs': len(entries), 'joint_two_pairs': sum(e['joint_cost'] == 2 for e in entries),
                                  'joint_three_pairs': sum(e['joint_cost'] == 3 for e in entries),
                                  'orbits': len(reps), 'joint_two_orbits': sum(e['joint_cost'] == 2 for e in reps),
                                  'joint_three_orbits': sum(e['joint_cost'] == 3 for e in reps)}
    return {'status': 'EXACT_FINITE_ENUMERATION', 'n': n, 'gate_lists_by_size': lists_by_size,
            'gate_lists_total': count, 'functions_cost_at_most_two': len(costs),
            'functions_cost_exactly_two': len(minimal_two), 'one_gate_targets': sorted(g_pairs),
            'pair_count': len(all_pairs), 'orbit_count': len(catalogue),
            'joint_two_pairs': sum(e['joint_cost'] == 2 for e in all_pairs.values()),
            'joint_three_pairs': sum(e['joint_cost'] == 3 for e in all_pairs.values()),
            'joint_two_orbits': sum(e['joint_cost'] == 2 for e in catalogue),
            'joint_three_orbits': sum(e['joint_cost'] == 3 for e in catalogue),
            'orbit_work': required_work, 'family_summary': family_summary, 'catalogue': catalogue,
            'model': 'Primary inputs only; no free constants or complements; binary NAND with repeated fanins and free fanout; any input/gate can be an output.',
            'truth_table_convention': 'Bit a is the output on xi=(a>>i)&1.',
            'scope': 'Complete bounded syntactic enumeration with independent Boolean witness validation. No SAT solver, Lean refinement, general scalarization, or P-vs-NP claim.'}


def source_sha256_lf(raw=None):
    if raw is None: raw = Path(__file__).read_bytes()
    if type(raw) is not bytes: raise ValueError('bytes required')
    return hashlib.sha256(raw.replace(b'\r\n', b'\n').replace(b'\r', b'\n')).hexdigest()


def build_report():
    result = build_catalogue(5)
    result['source_sha256_lf'] = source_sha256_lf()
    result['hash_normalization'] = 'CRLF and CR converted to LF before SHA-256'
    return result


if __name__ == '__main__':
    print(json.dumps(build_report(), indent=2, sort_keys=True))
