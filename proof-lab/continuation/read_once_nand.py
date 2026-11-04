"""Bounded strict read-once NAND recognition by signed-cofactor dynamic programming.

No constants, negations, or output complements are free. A positive input is
an accepted leaf. This implementation refuses inputs beyond five variables;
resource refusal is never a negative mathematical result. See READ_ONCE_NAND.md.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path

@dataclass(frozen=True)
class Limits:
    max_n: int = 5
    max_states: int = 512
    max_table_lookups: int = 1_000_000

class _Limit(Exception):
    pass

class _Search:
    def __init__(self, limits):
        self.limits = limits
        self.lookups = 0
        self.partitions = 0
        self.memo_hits = 0
        self.memo = {}

    def bit(self, mask, assignment):
        if self.lookups >= self.limits.max_table_lookups:
            raise _Limit('table lookup cap')
        self.lookups += 1
        return (mask >> assignment) & 1

    def compress(self, variables, mask):
        k = len(variables)
        keep = []
        for i in range(k):
            essential = False
            for a in range(1 << k):
                if not ((a >> i) & 1) and self.bit(mask, a) != self.bit(mask, a | (1 << i)):
                    essential = True
                    break
            if essential:
                keep.append(i)
        small = 0
        for a in range(1 << len(keep)):
            original = sum(((a >> j) & 1) << i for j, i in enumerate(keep))
            small |= self.bit(mask, original) << a
        return tuple(variables[i] for i in keep), small

    def solve(self, variables, mask):
        variables, mask = self.compress(variables, mask)
        key = variables, mask
        if key in self.memo:
            self.memo_hits += 1
            return self.memo[key]
        if len(self.memo) >= self.limits.max_states:
            raise _Limit('state cap')
        self.memo[key] = None
        k = len(variables)
        if k == 0:
            return None
        if k == 1:
            tree = ('input', variables[0]) if mask == 2 else None
            self.memo[key] = tree
            return tree
        zero = next((a for a in range(1 << k) if self.bit(mask, a) == 0), None)
        if zero is None:
            return None
        # NAND is commutative: keep position zero on the left to avoid repeats.
        for left_bits in range(1, 1 << k):
            if not (left_bits & 1) or left_bits == (1 << k)-1:
                continue
            self.partitions += 1
            left = tuple(i for i in range(k) if (left_bits >> i) & 1)
            right = tuple(i for i in range(k) if not ((left_bits >> i) & 1))
            left_embeddings = [sum(((a >> j) & 1) << i for j, i in enumerate(left))
                               for a in range(1 << len(left))]
            right_embeddings = [sum(((a >> j) & 1) << i for j, i in enumerate(right))
                                for a in range(1 << len(right))]
            fixed_left = zero & left_bits
            fixed_right = zero & (((1 << k)-1) ^ left_bits)
            g = sum((1-self.bit(mask, a | fixed_right)) << u
                    for u, a in enumerate(left_embeddings))
            h = sum((1-self.bit(mask, fixed_left | b)) << v
                    for v, b in enumerate(right_embeddings))
            rectangle = True
            for u, a in enumerate(left_embeddings):
                for v, b in enumerate(right_embeddings):
                    if 1-self.bit(mask, a | b) != ((g >> u) & 1)*((h >> v) & 1):
                        rectangle = False
                        break
                if not rectangle:
                    break
            if not rectangle:
                continue
            g_tree = self.solve(tuple(variables[i] for i in left), g)
            if g_tree is None:
                continue
            h_tree = self.solve(tuple(variables[i] for i in right), h)
            if h_tree is None:
                continue
            tree = ('nand', g_tree, h_tree)
            self.memo[key] = tree
            return tree
        return None

    def counters(self):
        return {'table_lookups': self.lookups, 'partition_checks': self.partitions,
                'states': len(self.memo), 'memo_hits': self.memo_hits}

def _witness(tree, n):
    gates = []
    def emit(node):
        if node[0] == 'input':
            return node[1]
        left, right = emit(node[1]), emit(node[2])
        output = n + len(gates)
        gates.append([left, right])
        return output
    output = emit(tree)
    return {'gates': gates, 'output': output}

def recognize(n, mask, *, limits=Limits()):
    """Return READ_ONCE / NOT_READ_ONCE / MALFORMED / RESOURCE_LIMIT.

    Mask bit a is the output on x_i=(a>>i)&1. Essential inputs are determined
    exactly; the witness keeps their original input indices. On d>=1 essential
    inputs, READ_ONCE is equivalent to strict NAND complexity C(f)=d-1.
    table_lookups counts actual charged truth-table bit reads, not CPU steps.
    """
    counters = {'table_lookups': 0, 'partition_checks': 0, 'states': 0, 'memo_hits': 0}
    def result(status, reason, **extra):
        return {'status': status, 'reason': reason, 'counters': counters, **extra}
    if type(limits) is not Limits:
        return result('MALFORMED', 'limits must have exact Limits type')
    defaults = Limits()
    for name in ('max_n', 'max_states', 'max_table_lookups'):
        value = getattr(limits, name)
        if type(value) is not int or not 0 <= value <= getattr(defaults, name):
            return result('MALFORMED', 'limits must be exact nonnegative integers no higher than defaults')
    if type(n) is not int or n < 1 or type(mask) is not int or mask < 0:
        return result('MALFORMED', 'n must be a positive exact integer and mask a nonnegative exact integer')
    if n > limits.max_n:
        return result('RESOURCE_LIMIT', 'input variable cap')
    if mask.bit_length() > (1 << n):
        return result('MALFORMED', 'truth mask out of range')
    search = _Search(limits)
    try:
        essential, _ = search.compress(tuple(range(n)), mask)
        tree = search.solve(tuple(range(n)), mask)
    except _Limit as error:
        counters = search.counters()
        return result('RESOURCE_LIMIT', str(error))
    counters = search.counters()
    if tree is None:
        return result('NOT_READ_ONCE', 'no strict read-once NAND tree', essential_inputs=list(essential))
    witness = _witness(tree, n)
    return result('READ_ONCE', 'reconstructed positive-leaf NAND tree',
                  essential_inputs=list(essential), gate_count=len(witness['gates']), witness=witness)

def _mask_from_row_function(n, function):
    return sum(int(bool(function([(a >> i) & 1 for i in range(n)]))) << a
               for a in range(1 << n))

def source_sha256_lf():
    data = Path(__file__).read_bytes().replace(b'\r\n', b'\n').replace(b'\r', b'\n')
    return hashlib.sha256(data).hexdigest()

def report_digest(report):
    body = {k: v for k, v in report.items() if k != 'report_sha256'}
    raw = (json.dumps(body, sort_keys=True, separators=(',', ':'), ensure_ascii=True)+'\n').encode()
    return hashlib.sha256(raw).hexdigest()

def build_demo():
    def reused(v):
        z, a, b, c = v
        u = not (z and a)
        w = not ((not (z and b)) and c)
        return not (u and w)
    examples = [('positive_leaf', 1, 2), ('negative_leaf', 1, 1),
                ('paid_zero', 3, 0), ('paid_one', 3, 255),
                ('nand2', 2, 7), ('nand3_not_a_two_gate_tree', 3, 127),
                ('balanced4', 4, _mask_from_row_function(4, lambda x: (x[0] and x[1]) or (x[2] and x[3]))),
                ('reused_z_nonunate', 4, _mask_from_row_function(4, reused))]
    report = {'format': 'read-once-nand-demo-v1',
              'scope': 'Bounded exact table computation plus ordinary proof; not Lean-formalized or a P-vs-NP solution.',
              'table_encoding': 'bit assignment; assignment=sum_i x_i*2^i',
              'source_sha256_lf': source_sha256_lf(),
              'source_hash_normalization': 'CRLF->LF then CR->LF; other bytes unchanged',
              'report_hash_encoding': 'compact sorted-key ASCII JSON excluding report_sha256, one terminal LF',
              'limits': vars(Limits()),
              'examples': [{'name': name, 'n': n, 'mask': mask, 'result': recognize(n, mask)}
                           for name, n, mask in examples]}
    report['report_sha256'] = report_digest(report)
    return report

def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args(argv)
    report = build_demo()
    if args.write:
        path = Path(__file__).resolve().parent / 'results' / 'read-once-nand-demo.json'
        path.parent.mkdir(exist_ok=True)
        path.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps({'source_sha256_lf': report['source_sha256_lf'],
                      'report_sha256': report['report_sha256'],
                      'statuses': {row['name']: row['result']['status'] for row in report['examples']}}, sort_keys=True))
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
