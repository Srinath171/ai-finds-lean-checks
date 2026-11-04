"""Bounded scalar profiles for the complete C(f)=2, one-NAND-g catalogue."""
from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path
import time
from continuation.low_cost_two import build_catalogue, permute_mask
from hour2.joint_nand import compute_all


def valid_int(x, low, high): return type(x) is int and low <= x <= high


def evaluate(n, witness):
    if not valid_int(n, 1, 5) or type(witness) is not dict or set(witness) != {'gates', 'outputs'}: raise ValueError('bad witness')
    gates, outputs = witness['gates'], witness['outputs']
    if type(gates) is not list or len(gates) > 11 or type(outputs) is not list or not 1 <= len(outputs) <= 2: raise ValueError('bad shape')
    for k, pair in enumerate(gates):
        if type(pair) is not list or len(pair) != 2 or any(not valid_int(i, 0, n+k-1) for i in pair): raise ValueError('bad topology')
    if any(not valid_int(i, 0, n+len(gates)-1) for i in outputs): raise ValueError('bad output')
    result = [0] * len(outputs)
    for a in range(1 << n):
        signals = [bool((a >> i) & 1) for i in range(n)]
        for left, right in gates: signals.append(not (signals[left] and signals[right]))
        for j, out in enumerate(outputs):
            if signals[out]: result[j] += 1 << a
    return result


def remap(witness, old_n, new_n, mapping):
    change = lambda i: mapping[i] if i < old_n else new_n+i-old_n
    return {'gates': [[change(a), change(b)] for a, b in witness['gates']], 'outputs': [change(i) for i in witness['outputs']]}


def normalize(mask, witness):
    if not valid_int(mask, 0, (1 << 32)-1) or evaluate(5, witness) != [mask]: raise ValueError('bad source target')
    support = [i for i in range(5) if any(((mask >> a) & 1) != ((mask >> (a ^ (1 << i))) & 1) for a in range(32))]
    n = max(1, len(support))
    mapping = [support.index(i) if i in support else 0 for i in range(5)]
    reduced_witness = remap(witness, 5, n, mapping)
    reduced = evaluate(n, reduced_witness)[0]
    canonical, permutation = min((permute_mask(n, reduced, p), p) for p in itertools.permutations(range(n)))
    canonical_witness = remap(reduced_witness, n, n, permutation)
    if evaluate(n, canonical_witness) != [canonical]: raise AssertionError('renaming failure')
    return n, canonical, canonical_witness


def build_targets():
    catalogue = build_catalogue(5)
    if catalogue['status'] != 'EXACT_FINITE_ENUMERATION': raise AssertionError('catalogue incomplete')
    h_witnesses = compute_all(2)['singles']
    targets, profiles = {}, []
    for index, pair in enumerate(catalogue['catalogue']):
        keys = []
        base = pair['joint_witness']
        for h in range(16):
            scalar = h_witnesses[h]['witness']
            mapping = lambda i: base['outputs'][i] if i < 2 else 5+len(base['gates'])+i-2
            witness = {'gates': base['gates'] + [[mapping(a), mapping(b)] for a, b in scalar['gates']],
                       'outputs': [mapping(scalar['outputs'][0])]}
            mask = sum(((h >> (((pair['f'] >> a) & 1)+2*((pair['g'] >> a) & 1))) & 1) << a for a in range(32))
            n, canonical, normalized = normalize(mask, witness)
            key = f'{n}:{canonical}'
            upper = len(normalized['gates'])
            if upper > 8: raise AssertionError('composition exceeded eight gates')
            if key not in targets or upper < targets[key]['constructive_upper_bound']:
                targets[key] = {'variables': n, 'mask': canonical, 'constructive_upper_bound': upper,
                                'constructive_witness': normalized, 'construction_source': {'pair_index': index, 'h': h}}
            keys.append(key)
        profiles.append({'pair_index': index, 'f': pair['f'], 'g': pair['g'], 'joint_cost': pair['joint_cost'], 'target_keys': keys})
    return targets, profiles


def lf_hash(path):
    raw = Path(path).read_bytes().replace(b'\r\n', b'\n').replace(b'\r', b'\n')
    return hashlib.sha256(raw).hexdigest()


def cached_costs(targets):
    small = {n: compute_all(n)['singles'] for n in (1, 2)}
    path = 'continuation/results/profile-n3.json'
    saved = json.loads(Path(path).read_text())
    if saved['source_sha256_lf'] != lf_hash('continuation/profile_sat.py'): raise ValueError('stale n3 cache source')
    if saved['n'] != 3: raise ValueError('wrong cache dimension')
    entries = {e['canonical_mask']: e for e in saved['ordinary_cache']}
    results = {}
    for key, target in targets.items():
        n, mask = target['variables'], target['mask']
        if n > 3: continue
        if n < 3:
            entry = small[n][mask]
            witness = {k: entry['witness'][k] for k in ('gates', 'outputs')}
            cost, status = entry['cost'], 'EXACT_FINITE_ENUMERATION'
            evidence = {'source': 'complete_n1_n2_state_BFS'}
        else:
            entry = entries[mask]
            if entry['status'] != 'EXACT_SOLVER_EVIDENCE': raise ValueError('unknown cache entry')
            cost, witness, status = entry['cost'], entry['witness'], 'EXACT_Z3_CACHE'
            if not valid_int(cost, 0, 10): raise ValueError('bad cached cost')
            indices = entry['query_indices']
            if type(indices) is not list or any(not valid_int(i, 0, len(saved['queries'])-1) for i in indices): raise ValueError('bad cache indices')
            chain = [saved['queries'][i] for i in indices]
            if [q['gate_bound'] for q in chain] != list(range(cost+1)) or [q['targets'] for q in chain] != [[mask]]*(cost+1) or [q['status'] for q in chain] != ['UNSAT']*cost+['SAT']: raise ValueError('unproved cached minimum')
            evidence = {'source': path, 'artifact_sha256_lf': lf_hash(path), 'query_indices': indices}
        if evaluate(n, witness) != [mask] or len(witness['gates']) != cost or cost > target['constructive_upper_bound']: raise ValueError('cached witness mismatch')
        results[key] = {'status': status, 'cost': cost, 'lower_bound': cost, 'upper_bound': cost, 'witness': witness, 'evidence': evidence, 'query_indices': []}
    return results


class Refusal(Exception): pass


class Engine:
    """One-output Boolean CNF; any earlier signals and any output are allowed."""
    def __init__(self, n, gates, deadline):
        if not valid_int(n, 1, 5) or not valid_int(gates, 0, 8): raise ValueError('bad dimensions')
        import z3
        self.z3, self.n, self.gates = z3, n, gates
        self.solver = z3.Solver(); self.solver.set(random_seed=0)
        self.choices = []
        clauses = 0
        def add(*args):
            nonlocal clauses
            clauses += 1
            if clauses % 100 == 0 and time.monotonic() >= deadline: raise Refusal('wall_clock_cap')
            self.solver.add(z3.Or(*args))
        def onehot(values):
            add(*values)
            for a, b in itertools.combinations(values, 2): add(z3.Not(a), z3.Not(b))
        signals = [[z3.BoolVal(bool((a >> i) & 1)) for a in range(1 << n)] for i in range(n)]
        for k in range(gates):
            if time.monotonic() >= deadline: raise Refusal('wall_clock_cap')
            values = [z3.Bool(f'v{k}_{a}') for a in range(1 << n)]
            pairs = list(itertools.combinations_with_replacement(range(n+k), 2))
            choices = [z3.Bool(f'p{k}_{a}_{b}') for a, b in pairs]
            onehot(choices)
            for selector, (a, b) in zip(choices, pairs):
                for row in range(1 << n):
                    add(z3.Not(selector), values[row], signals[a][row])
                    add(z3.Not(selector), values[row], signals[b][row])
                    add(z3.Not(selector), z3.Not(values[row]), z3.Not(signals[a][row]), z3.Not(signals[b][row]))
            signals.append(values); self.choices.append((pairs, choices))
        self.outputs = [z3.Bool(f'out{i}') for i in range(n+gates)]
        self.truth = [z3.Bool(f'target{a}') for a in range(1 << n)]
        onehot(self.outputs)
        for i, selector in enumerate(self.outputs):
            for row in range(1 << n):
                add(z3.Not(selector), z3.Not(self.truth[row]), signals[i][row])
                add(z3.Not(selector), self.truth[row], z3.Not(signals[i][row]))

    def query(self, mask, timeout_ms):
        if not valid_int(mask, 0, (1 << (1 << self.n))-1) or not valid_int(timeout_ms, 1, 5000): raise ValueError('bad query')
        z3 = self.z3; self.solver.set(timeout=timeout_ms)
        assumptions = [v if ((mask >> a) & 1) else z3.Not(v) for a, v in enumerate(self.truth)]
        started = time.monotonic(); status = self.solver.check(*assumptions)
        result = {'variables': self.n, 'mask': mask, 'gate_bound': self.gates, 'status': str(status).upper(), 'elapsed_seconds': round(time.monotonic()-started, 6)}
        if status == z3.sat:
            model = self.solver.model()
            gates = [[a, b] for pairs, choices in self.choices for (a, b), selector in zip(pairs, choices) if z3.is_true(model.eval(selector))]
            outputs = [i for i, selector in enumerate(self.outputs) if z3.is_true(model.eval(selector))]
            witness = {'gates': gates, 'outputs': outputs}
            if len(gates) != self.gates or evaluate(self.n, witness) != [mask]: raise AssertionError('solver witness rejected')
            result['witness'] = witness
        return result


def initial_record(target):
    if type(target) is not dict or not valid_int(target.get('variables'), 1, 5) or not valid_int(target.get('constructive_upper_bound'), 0, 8): raise ValueError('bad target dimensions')
    if not valid_int(target.get('mask'), 0, (1 << (1 << target['variables']))-1): raise ValueError('bad target mask')
    if evaluate(target['variables'], target['constructive_witness']) != [target['mask']]: raise ValueError('invalid constructive witness')
    if len(target['constructive_witness']['gates']) != target['constructive_upper_bound']: raise ValueError('bad upper bound')
    return {'status': 'UNKNOWN', 'cost': None, 'lower_bound': 0, 'upper_bound': target['constructive_upper_bound'],
            'witness': target['constructive_witness'], 'query_indices': []}


def solve_target(target, record, ask):
    """An UNKNOWN stops this target; its verified upper witness is retained."""
    for bound in range(target['constructive_upper_bound']):
        result, index = ask(target['variables'], target['mask'], bound)
        record['query_indices'].append(index)
        if result['status'] == 'UNSAT': record['lower_bound'] = bound+1
        elif result['status'] == 'SAT':
            witness = result['witness']
            if evaluate(target['variables'], witness) != [target['mask']] or len(witness['gates']) != bound: raise AssertionError('SAT witness mismatch')
            record.update(status='EXACT_Z3_NEW', cost=bound, lower_bound=bound, upper_bound=bound, witness=witness)
            return
        else:
            record['unknown_reason'] = 'solver_unknown_or_timeout'
            return
    cost = target['constructive_upper_bound']
    record.update(status='EXACT_Z3_NEW', cost=cost, lower_bound=cost, upper_bound=cost)
    record['evidence'] = 'UNSAT at every smaller bound; independently evaluated constructive witness at upper bound'


def compare_profiles(profiles, results):
    compared, unresolved, counterexamples = [], [], []
    for a, b in itertools.combinations(profiles, 2):
        if a['joint_cost'] == b['joint_cost']: continue
        separator = next((h for h, (ka, kb) in enumerate(zip(a['target_keys'], b['target_keys']))
                          if results[ka]['upper_bound'] < results[kb]['lower_bound'] or results[kb]['upper_bound'] < results[ka]['lower_bound']), None)
        pair = {'pair_indices': [a['pair_index'], b['pair_index']], 'joint_costs': [a['joint_cost'], b['joint_cost']]}
        if separator is not None:
            pair['separating_h'] = separator; compared.append(pair)
        else:
            exact = all(results[k]['cost'] is not None for k in a['target_keys']+b['target_keys'])
            if exact:
                pair['profile'] = [results[k]['cost'] for k in a['target_keys']]; counterexamples.append(pair)
            else: unresolved.append(pair)
    return {'separated_cross_joint_pairs': compared, 'unresolved_cross_joint_pairs': unresolved, 'counterexamples': counterexamples}


def run_pass(*, seconds=300, query_ms=500, max_queries=350):
    if not valid_int(seconds, 1, 300) or not valid_int(query_ms, 1, 5000) or not valid_int(max_queries, 1, 350): raise ValueError('invalid limits')
    started = time.monotonic(); deadline = started+seconds
    targets, profiles = build_targets()
    results = cached_costs(targets)
    known_count = len(results)
    queries, engines = [], {}
    refusal = None
    for key, target in targets.items():
        if key not in results: results[key] = initial_record(target)
    def ask(n, mask, bound):
        if len(queries) >= max_queries: raise Refusal('query_cap')
        if time.monotonic() >= deadline: raise Refusal('wall_clock_cap')
        key = n, bound
        if key not in engines: engines[key] = Engine(n, bound, deadline)
        remaining = int((deadline-time.monotonic())*1000)
        if remaining < 1: raise Refusal('wall_clock_cap')
        result = engines[key].query(mask, min(query_ms, remaining))
        queries.append(result)
        return result, len(queries)-1
    try:
        for key in sorted(targets, key=lambda k:(targets[k]['variables'], targets[k]['constructive_upper_bound'], targets[k]['mask'])):
            if results[key]['cost'] is not None: continue
            solve_target(targets[key], results[key], ask)
            print(json.dumps({'target': key, 'status': results[key]['status'], 'interval': [results[key]['lower_bound'], results[key]['upper_bound']], 'queries': len(queries)}), flush=True)
    except Refusal as exc: refusal = str(exc)
    comparisons = compare_profiles(profiles, results)
    status = 'COUNTEREXAMPLE_SOLVER_EVIDENCE' if comparisons['counterexamples'] else ('NO_CROSS_J_COLLISION_IN_FINITE_C2_CATALOGUE' if not comparisons['unresolved_cross_joint_pairs'] else 'PARTIAL_UNKNOWN')
    return {'status': status, 'limits': {'seconds': seconds, 'query_ms': query_ms, 'max_queries': max_queries},
            'elapsed_seconds': round(time.monotonic()-started, 6), 'refusal': refusal,
            'cached_exact_targets': known_count, 'total_targets': len(targets), 'targets_by_variables': dict(Counter(t['variables'] for t in targets.values())),
            'exact_targets': sum(r['cost'] is not None for r in results.values()), 'unknown_targets': sum(r['cost'] is None for r in results.values()),
            'targets': targets, 'cost_results': results, 'profiles': profiles, 'comparisons': comparisons, 'queries': queries,
            'source_sha256_lf': lf_hash(__file__), 'catalogue_source_sha256_lf': lf_hash('continuation/low_cost_two.py'),
            'n3_cache_sha256_lf': lf_hash('continuation/results/profile-n3.json'),
            'scope': 'Bounded finite C(f)=2 catalogue only. Verified circuit witnesses support upper bounds; new and cached Z3 UNSAT results support lower bounds without formal proof certificates. UNKNOWN remains an interval and is never assigned its upper bound as an exact cost. No general scalarization or P-vs-NP conclusion.'}


def nand_cases():
    targets, profiles = build_targets()
    wide, two_gate = [], []
    for pair in profiles:
        key = pair['target_keys'][7]
        target = targets[key]
        entry = {'pair_index': pair['pair_index'], 'f': pair['f'], 'g': pair['g'],
                 'joint_cost': pair['joint_cost'], 'target_key': key, **target}
        if pair['joint_cost'] == 2:
            if target['constructive_upper_bound'] > 3: raise AssertionError('NAND of a two-gate joint pair must cost at most three')
            two_gate.append(entry)
        if target['variables'] > 3:
            if pair['joint_cost'] != 3 or target['constructive_upper_bound'] != 4: raise AssertionError('unexpected wide NAND case')
            wide.append(entry)
    if len(wide) != 6 or len(two_gate) != 5 or len({e['target_key'] for e in wide}) != 6: raise AssertionError('unexpected case count')
    return wide, two_gate


def run_nand_pass(*, seconds=300, query_ms=500, max_queries=12):
    if not valid_int(seconds, 1, 300) or not valid_int(query_ms, 1, 5000) or not valid_int(max_queries, 1, 12): raise ValueError('invalid narrow-pass limits')
    started = time.monotonic(); deadline = started+seconds
    cases, j2_cases = nand_cases()
    records = [initial_record(case) for case in cases]
    engines, queries, refusal = {}, [], None
    try:
        for case, record in zip(cases, records):
            for bound in (3, 4):
                if len(queries) >= max_queries: raise Refusal('query_cap')
                if time.monotonic() >= deadline: raise Refusal('wall_clock_cap')
                key = case['variables'], bound
                if key not in engines: engines[key] = Engine(case['variables'], bound, deadline)
                remaining = int((deadline-time.monotonic())*1000)
                if remaining < 1: raise Refusal('wall_clock_cap')
                result = engines[key].query(case['mask'], min(query_ms, remaining))
                queries.append(result); record['query_indices'].append(len(queries)-1)
                if result['status'] == 'SAT':
                    if len(result['witness']['gates']) != bound or evaluate(case['variables'], result['witness']) != [case['mask']]: raise AssertionError('SAT witness rejected')
                    if bound == 3:
                        record.update(status='SHORTER_WITNESS_FOUND', cost=None, upper_bound=3, witness=result['witness'])
                elif result['status'] == 'UNSAT':
                    if bound == 4: raise AssertionError('solver rejected an independently checked four-gate witness')
                    record.update(status='EXACT_Z3_NEW', cost=4, lower_bound=4, upper_bound=4,
                                  evidence='UNSAT at most three; independently evaluated four-gate construction')
            print(json.dumps({'target': case['target_key'], 'status': record['status'], 'queries': len(queries)}), flush=True)
    except Refusal as exc: refusal = str(exc)
    status = 'ALL_SIX_NAND_COST_FOUR_SOLVER_EVIDENCE' if all(r['cost'] == 4 for r in records) else ('SHORTER_WITNESS_FOUND' if any(r['upper_bound'] < 4 for r in records) else 'PARTIAL_UNKNOWN')
    return {'status': status, 'mode': 'six_support4_or5_NAND_coordinates_only',
            'limits': {'seconds':seconds,'query_ms':query_ms,'max_queries':max_queries},
            'elapsed_seconds':round(time.monotonic()-started,6),'refusal':refusal,
            'cases':[{**case,'cost_result':record} for case,record in zip(cases,records)],
            'joint_cost_two_cases_with_NAND_upper_at_most_three':j2_cases,
            'queries':queries,'source_sha256_lf':lf_hash(__file__),
            'catalogue_source_sha256_lf':lf_hash('continuation/low_cost_two.py'),
            'scope':'Only six support4/5 NAND profile coordinates were queried, at bounds3 and4. A six-case cost-four result uses Z3 UNSAT evidence plus independently evaluated upper witnesses; it separates those cases from the five J=2 catalogue classes at this one coordinate. No full44-target campaign, general scalarization, or formal UNSAT proof is claimed.'}


if __name__ == '__main__':
    report = run_nand_pass()
    Path('continuation/results/low-cost-nand-six.json').write_text(json.dumps(report, indent=2, sort_keys=True)+'\n', encoding='utf-8')
    print(json.dumps({k:report[k] for k in ('status','elapsed_seconds','mode','refusal')}), flush=True)
