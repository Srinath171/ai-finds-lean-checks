"""Bounded n<=3 joint-cost/profile investigation; all lower bounds are SAT evidence."""
from __future__ import annotations
from collections import defaultdict
import hashlib
import itertools
import json
from pathlib import Path
import time


def integer(x, lo, hi):
    return type(x) is int and lo <= x <= hi


def inputs(n):
    return [sum(1 << a for a in range(1 << n) if (a >> i) & 1) for i in range(n)]


def permutation_mask(n, mask, permutation):
    if not integer(n, 1, 3) or not integer(mask, 0, (1 << (1 << n)) - 1):
        raise ValueError('invalid n or mask')
    if type(permutation) is not tuple or any(type(i) is not int for i in permutation) or sorted(permutation) != list(range(n)):
        raise ValueError('invalid permutation')
    answer = 0
    for a in range(1 << n):
        original = sum(((a >> permutation[i]) & 1) << i for i in range(n))
        answer |= ((mask >> original) & 1) << a
    return answer


def combine(n, f, g, h):
    if not integer(n, 1, 3) or not all(integer(t, 0, (1 << (1 << n)) - 1) for t in (f, g)) or not integer(h, 0, 15):
        raise ValueError('invalid combination')
    return sum(((h >> (((f >> a) & 1) + 2 * ((g >> a) & 1))) & 1) << a for a in range(1 << n))


def evaluate(n, witness):
    if not integer(n, 1, 3) or type(witness) is not dict or set(witness) != {'gates', 'outputs'}:
        raise ValueError('invalid witness')
    gates, outputs = witness['gates'], witness['outputs']
    if type(gates) is not list or len(gates) > 11 or type(outputs) is not list or not 1 <= len(outputs) <= 2:
        raise ValueError('invalid witness dimensions')
    for k, pair in enumerate(gates):
        if type(pair) is not list or len(pair) != 2 or any(not integer(i, 0, n + k - 1) for i in pair):
            raise ValueError('invalid topology')
    if any(not integer(i, 0, n + len(gates) - 1) for i in outputs):
        raise ValueError('invalid outputs')
    tables = [[] for _ in range(n + len(gates))]
    for a in range(1 << n):
        values = [bool((a >> i) & 1) for i in range(n)]
        for left, right in gates:
            values.append(not (values[left] and values[right]))
        for k, value in enumerate(values):
            tables[k].append(value)
    masks = [sum(1 << a for a, v in enumerate(table) if v) for table in tables]
    return [masks[i] for i in outputs], masks


def verify(n, targets, witness):
    if type(targets) is not list or not integer(n, 1, 3) or any(not integer(t, 0, (1 << (1 << n)) - 1) for t in targets):
        return False
    try:
        observed, _ = evaluate(n, witness)
        return observed == targets
    except (ValueError, TypeError):
        return False


class Refusal(Exception):
    pass


class BooleanEngine:
    """Incremental pure-Boolean engine; target truth bits are assumptions."""
    def __init__(self, n, gates, outputs=1, *, deadline=None):
        if not integer(n, 1, 3) or not integer(gates, 0, 10) or not integer(outputs, 1, 2):
            raise ValueError('invalid engine dimensions')
        import z3
        self.z3, self.n, self.gates, self.outputs = z3, n, gates, outputs
        self.solver = z3.Solver()
        self.solver.set(random_seed=0)
        self.signals = [[z3.BoolVal(bool((a >> i) & 1)) for a in range(1 << n)] for i in range(n)]
        self.choices, self.selectors, self.truth = [], [], []
        def add(*terms): self.solver.add(z3.Or(*terms))
        def one_hot(values):
            add(*values)
            for a, b in itertools.combinations(values, 2): add(z3.Not(a), z3.Not(b))
        for k in range(gates):
            if deadline is not None and time.monotonic() >= deadline: raise Refusal('deadline')
            truth = [z3.Bool(f'v_{k}_{a}') for a in range(1 << n)]
            pairs = list(itertools.combinations_with_replacement(range(n + k), 2))
            selectors = [z3.Bool(f'p_{k}_{a}_{b}') for a, b in pairs]
            one_hot(selectors)
            for selector, (left, right) in zip(selectors, pairs):
                for a in range(1 << n):
                    add(z3.Not(selector), truth[a], self.signals[left][a])
                    add(z3.Not(selector), truth[a], self.signals[right][a])
                    add(z3.Not(selector), z3.Not(truth[a]), z3.Not(self.signals[left][a]), z3.Not(self.signals[right][a]))
            self.signals.append(truth)
            self.choices.append((pairs, selectors))
        for out in range(outputs):
            truth = [z3.Bool(f't_{out}_{a}') for a in range(1 << n)]
            selectors = [z3.Bool(f'o_{out}_{i}') for i in range(n + gates)]
            one_hot(selectors)
            for i, selector in enumerate(selectors):
                for a in range(1 << n):
                    add(z3.Not(selector), z3.Not(truth[a]), self.signals[i][a])
                    add(z3.Not(selector), truth[a], z3.Not(self.signals[i][a]))
            self.selectors.append(selectors)
            self.truth.append(truth)

    def query(self, targets, timeout_ms=1000):
        if type(targets) is not list or len(targets) != self.outputs or any(not integer(t, 0, (1 << (1 << self.n)) - 1) for t in targets) or not integer(timeout_ms, 1, 30000):
            raise ValueError('invalid query')
        z3 = self.z3
        self.solver.set(timeout=timeout_ms)
        assumptions = [truth[a] if ((target >> a) & 1) else z3.Not(truth[a])
                       for target, truth in zip(targets, self.truth) for a in range(1 << self.n)]
        start = time.monotonic()
        answer = self.solver.check(*assumptions)
        result = {'targets': targets, 'gate_bound': self.gates, 'status': str(answer).upper(),
                  'elapsed_seconds': round(time.monotonic() - start, 6)}
        if answer == z3.sat:
            model = self.solver.model()
            gates = [[a, b] for pairs, selectors in self.choices for (a, b), s in zip(pairs, selectors) if z3.is_true(model.eval(s))]
            outputs = [next(i for i, s in enumerate(selectors) if z3.is_true(model.eval(s))) for selectors in self.selectors]
            witness = {'gates': gates, 'outputs': outputs}
            if len(gates) != self.gates or not verify(self.n, targets, witness):
                raise AssertionError('independent witness rejected')
            result['witness'] = witness
        return result


class Investigation:
    def __init__(self, n=3, *, seconds=300, max_gates=10, query_ms=1000, max_queries=1000):
        if not integer(n, 1, 3) or not integer(seconds, 1, 900) or not integer(max_gates, 0, 10) or not integer(query_ms, 1, 30000) or not integer(max_queries, 1, 2000):
            raise ValueError('invalid limits')
        self.n, self.max_gates, self.query_ms, self.max_queries = n, max_gates, query_ms, max_queries
        self.started, self.seconds = time.monotonic(), seconds
        self.deadline = self.started + seconds
        self.engines, self.cache, self.queries = {}, {}, []
        self.permutations = list(itertools.permutations(range(n)))
        self.full = (1 << (1 << n)) - 1
        self.gs = sorted({self.full ^ (a & b) for a in inputs(n) for b in inputs(n)})

    def canonical(self, mask):
        return min((permutation_mask(self.n, mask, p), p) for p in self.permutations)

    def query(self, targets, bound):
        if len(self.queries) >= self.max_queries: raise Refusal('query_cap')
        if time.monotonic() >= self.deadline: raise Refusal('deadline')
        key = bound, len(targets)
        if key not in self.engines:
            self.engines[key] = BooleanEngine(self.n, bound, len(targets), deadline=self.deadline)
        remaining_ms = int((self.deadline - time.monotonic()) * 1000)
        if remaining_ms < 1: raise Refusal('deadline')
        result = self.engines[key].query(targets, min(self.query_ms, remaining_ms))
        self.queries.append(result)
        return result

    def ordinary(self, mask):
        canonical, permutation = self.canonical(mask)
        if canonical not in self.cache:
            attempts = []
            entry = {'canonical_mask': canonical, 'status': 'UNKNOWN'}
            for bound in range(self.max_gates + 1):
                result = self.query([canonical], bound)
                attempts.append(len(self.queries) - 1)
                if result['status'] == 'SAT':
                    entry.update(status='EXACT_SOLVER_EVIDENCE', cost=bound, witness=result['witness'])
                    break
                if result['status'] != 'UNSAT': break
            entry['query_indices'] = attempts
            self.cache[canonical] = entry
        entry = self.cache[canonical]
        if entry['status'] != 'EXACT_SOLVER_EVIDENCE': return None
        inverse = [permutation.index(i) for i in range(self.n)]
        remap = lambda i: inverse[i] if i < self.n else i
        witness = {'gates': [[remap(a), remap(b)] for a, b in entry['witness']['gates']],
                   'outputs': [remap(entry['witness']['outputs'][0])]}
        if not verify(self.n, [mask], witness): raise AssertionError('input permutation rejected')
        return {'cost': entry['cost'], 'witness': witness, 'canonical_mask': canonical}

    def joint(self, f, g):
        if type(g) is not int or g not in self.gs: raise ValueError('g must be one primary-input NAND')
        ordinary = self.ordinary(f)
        if ordinary is None: return {'status': 'UNKNOWN'}
        cost, witness = ordinary['cost'], ordinary['witness']
        _, masks = evaluate(self.n, witness)
        if g in masks:
            answer = {'gates': witness['gates'], 'outputs': [witness['outputs'][0], masks.index(g)]}
            return {'status': 'EXACT_SOLVER_EVIDENCE', 'cost': cost, 'witness': answer,
                    'reason': 'ordinary_minimum_witness_already_contains_g'}
        if cost:
            result = self.query([f, g], cost)
            if result['status'] == 'UNKNOWN': return {'status': 'UNKNOWN', 'query_index': len(self.queries) - 1}
            if result['status'] == 'SAT': return {'status': 'EXACT_SOLVER_EVIDENCE', 'cost': cost, 'witness': result['witness'], 'query_index': len(self.queries) - 1}
        pair = next(([i, j] for i in range(self.n) for j in range(i, self.n)
                     if self.full ^ (inputs(self.n)[i] & inputs(self.n)[j]) == g), None)
        if pair is None: raise ValueError('g must be one primary-input NAND')
        answer = {'gates': witness['gates'] + [pair], 'outputs': [witness['outputs'][0], self.n + cost]}
        if not verify(self.n, [f, g], answer): raise AssertionError('appended witness rejected')
        return {'status': 'EXACT_SOLVER_EVIDENCE', 'cost': cost + 1, 'witness': answer,
                'reason': 'ordinary_lower_bound_and_joint_UNSAT_then_append_g' if cost else 'g_requires_one_gate',
                'query_index': len(self.queries) - 1 if cost else None}

    def run(self):
        groups, evaluated, collision, refusal = defaultdict(list), [], None, None
        all_pairs = sorted({min((permutation_mask(self.n, f, p), permutation_mask(self.n, g, p))
                                for p in self.permutations)
                            for f in range(self.full + 1) for g in self.gs})
        try:
            representatives = sorted({self.canonical(f)[0] for f in range(self.full + 1)})
            for f in representatives:
                self.ordinary(f)
                print(json.dumps({'ordinary_classes': len(self.cache), 'queries': len(self.queries)}), flush=True)
            for f, g in all_pairs:
                values = [self.ordinary(combine(self.n, f, g, h)) for h in range(16)]
                if all(v is not None for v in values):
                    profile = tuple(v['cost'] for v in values)
                    groups[profile].append((f, g))
            for profile, pairs in sorted(groups.items()):
                if len(pairs) < 2: continue
                local = []
                for f, g in pairs:
                    result = self.joint(f, g)
                    entry = {'f': f, 'g': g, 'profile': list(profile), 'joint': result}
                    evaluated.append(entry)
                    if result['status'] == 'EXACT_SOLVER_EVIDENCE':
                        for previous in local:
                            if previous['joint']['cost'] != result['cost']:
                                collision = [previous, entry]
                                break
                        local.append(entry)
                    if collision: break
                if collision: break
        except Refusal as exc:
            refusal = str(exc)
        exact = sum(e['status'] == 'EXACT_SOLVER_EVIDENCE' for e in self.cache.values())
        return {'status': 'FOUND_SOLVER_EVIDENCE' if collision else 'NO_COUNTEREXAMPLE_FOUND_IN_BOUNDED_RUN',
                'n': self.n, 'elapsed_seconds': round(time.monotonic() - self.started, 6),
                'limits': {'seconds': self.seconds, 'max_gates': self.max_gates, 'query_ms': self.query_ms, 'max_queries': self.max_queries},
                'refusal': refusal, 'ordinary_classes_exact': exact, 'ordinary_classes_seen': len(self.cache),
                'pair_orbits_total': len(all_pairs), 'pair_orbits_with_full_exact_profile': sum(map(len, groups.values())),
                'distinct_exact_profiles': len(groups), 'joint_pairs_queried_or_certified': evaluated,
                'counterexample': collision, 'ordinary_cache': list(self.cache.values()), 'queries': self.queries,
                'scope': 'Bounded finite investigation. Lower bounds are Z3 solver evidence, not formal proofs. Unknown queries/costs are excluded; absence of a found pair does not establish any general scalarization.'}


def source_hash():
    raw = Path(__file__).read_bytes().replace(b'\r\n', b'\n').replace(b'\r', b'\n')
    return hashlib.sha256(raw).hexdigest()


if __name__ == '__main__':
    report = Investigation().run()
    report['source_sha256_lf'] = source_hash()
    Path('continuation/results/profile-n3.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n', encoding='utf-8')
    print(json.dumps({k: report[k] for k in ('status', 'ordinary_classes_exact', 'pair_orbits_with_full_exact_profile', 'distinct_exact_profiles', 'counterexample')}), flush=True)
