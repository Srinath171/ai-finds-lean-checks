"""Independent bounded NAND enumeration; no SAT, cached costs, or classification.

Completeness: every k-gate DAG has a topological order. Its next gate is a
NAND of two earlier wires; commutativity permits i<=j. Enumerating every
such pair and every prefix through k=3 includes every circuit through
three gates, even those with repeated or unused gates. Recording every
wire includes all free output selectors. Missing scalar masks therefore
have cost at least four, which is precisely the truncated value required.

Global C(f)=2 justification (ordinary mathematics, not a Lean theorem):
retain Ess(f) and the fanins of g. Replacing all other inputs by one
retained input preserves the two targets and all scalar compositions.
The retained set is nonempty because g is nonconstant. Padding back adds
no cost, including for zero-essential scalar constants. Thus combined
support <=3 embeds into n=3 with every strict-NAND cost unchanged.
For combined support4/5, the separate six-case classification proves
C(NAND(f,g))=4; any J=2 pair gives that cost<=3. Those pairs cannot match
one of the five good truncated signatures. Together with this complete
finite n=3 check, this gives the global C2 decoder. No general-cost
profile theorem, source refinement, or P-versus-NP conclusion is claimed.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path

REPORT_PATH = Path(__file__).resolve().parent / 'results' / 'c2-truncated-n3.json'
HASH_ENCODING = 'UTF-8 compact sorted-key ASCII JSON excluding report_sha256, followed by one LF'

def _bounds(n, gate_bound):
    if type(n) is not int or not 1 <= n <= 3:
        raise ValueError('n must be an exact integer from1 through3')
    if type(gate_bound) is not int or not 0 <= gate_bound <= 3:
        raise ValueError('gate_bound must be an exact integer from0 through3')

def input_masks(n):
    _bounds(n, 0)
    return tuple(sum(((assignment >> i) & 1) << assignment
                     for assignment in range(1 << n)) for i in range(n))

def enumerate_low_cost(n=3, gate_bound=3):
    _bounds(n, gate_bound)
    full = (1 << (1 << n)) - 1
    inputs = input_masks(n)
    ordinary, joint = {}, {}
    ordinary_witnesses, joint_witnesses = {}, {}
    prefix_counts = [0] * (gate_bound + 1)
    def visit(wires, gates):
        depth = len(gates)
        prefix_counts[depth] += 1
        for i, f in enumerate(wires):
            if f not in ordinary or depth < ordinary[f]:
                ordinary[f] = depth
                ordinary_witnesses[f] = {'gates': gates, 'output': i}
            for j, g in enumerate(wires):
                key = (f, g)
                if key not in joint or depth < joint[key]:
                    joint[key] = depth
                    joint_witnesses[key] = {'gates': gates, 'outputs': (i, j)}
        if depth == gate_bound:
            return
        for i in range(len(wires)):
            for j in range(i, len(wires)):
                value = full ^ (wires[i] & wires[j])
                visit(wires + (value,), gates + ((i, j),))
    visit(inputs, ())
    return {'n': n, 'gate_bound': gate_bound, 'inputs': inputs,
            'prefix_counts': prefix_counts, 'ordinary': ordinary,
            'joint': joint, 'ordinary_witnesses': ordinary_witnesses,
            'joint_witnesses': joint_witnesses}

def compose_mask(f, g, h, n=3):
    _bounds(n, 0)
    full = (1 << (1 << n)) - 1
    if any(type(v) is not int or not 0 <= v <= full for v in (f, g)):
        raise ValueError('f and g must be in-range exact integer masks')
    if type(h) is not int or not 0 <= h < 16:
        raise ValueError('h must be an exact integer from0 through15')
    cells = ((full ^ f) & (full ^ g), (full ^ f) & g,
             f & (full ^ g), f & g)
    out = 0
    for bit, cell in enumerate(cells):
        if (h >> bit) & 1:
            out |= cell
    return out

def transpose_h_index(h):
    """Translate h between 2*f+g and f+2*g truth-table indexing.

    This involution swaps h bits one and two, preserving NAND index seven.
    For an array indexed by h, legacy[h] = this[transpose_h_index(h)].
    """
    if type(h) is not int or not 0 <= h < 16:
        raise ValueError('h must be an exact integer from 0 through 15')
    return (h & 9) | ((h & 2) << 1) | ((h & 4) >> 1)

def source_sha256_lf():
    data = Path(__file__).read_bytes().replace(b'\r\n', b'\n').replace(b'\r', b'\n')
    return hashlib.sha256(data).hexdigest()

def report_digest(report):
    payload = {k: v for k, v in report.items() if k != 'report_sha256'}
    encoded = (json.dumps(payload, sort_keys=True, separators=(',', ':'),
                          ensure_ascii=True) + '\n').encode('utf-8')
    return hashlib.sha256(encoded).hexdigest()

def build_report():
    enumeration = enumerate_low_cost()
    ordinary, joint = enumeration['ordinary'], enumeration['joint']
    full = 255
    fs = sorted(f for f, cost in ordinary.items() if cost == 2)
    gs = sorted({full ^ (a & b) for a in enumeration['inputs']
                                  for b in enumeration['inputs']})
    records, grouped = [], {}
    for f in fs:
        for g in gs:
            profile = [ordinary.get(compose_mask(f, g, h), 4) for h in range(16)]
            if (f, g) not in joint:
                raise RuntimeError('complete enumeration did not supply expected joint witness')
            record = {'f': f, 'g': g, 'joint_cost': joint[(f, g)],
                      'truncated_profile': profile,
                      'joint_witness': enumeration['joint_witnesses'][(f, g)]}
            records.append(record)
            grouped.setdefault(tuple(profile), []).append((f, g, joint[(f, g)]))
    classes = []
    for profile, members in sorted(grouped.items()):
        labels = sorted({j for _, _, j in members})
        classes.append({'truncated_profile': list(profile), 'joint_labels': labels,
                        'representative': {'f': members[0][0], 'g': members[0][1]},
                        'members': [{'f': f, 'g': g, 'joint_cost': j} for f, g, j in members]})
    good = [r['truncated_profile'] for r in classes if r['joint_labels'] == [2]]
    bad = [r['truncated_profile'] for r in classes if r['joint_labels'] == [3]]
    collisions = [r for r in classes if len(r['joint_labels']) > 1]
    report = {'format': 'c2-truncated-n3-v1', 'n': 3, 'gate_bound': 3,
              'scope': 'Complete finite enumeration, not a Lean proof or general-cost determinacy theorem.',
              'truth_mask_encoding': 'bit assignment; assignment=sum_i x_i*2^i',
              'h_encoding': 'bit0=h(0,0), bit1=h(0,1), bit2=h(1,0), bit3=h(1,1); NAND is7',
              'legacy_h_encoding': 'Earlier profile_sat/low_cost_profiles use bit index f+2*g; this report uses 2*f+g.',
              'legacy_profile_mapping': 'legacy[h]=this[legacy_to_this_h_index[h]]; permutation swaps h bits1 and2.',
              'legacy_to_this_h_index': [transpose_h_index(h) for h in range(16)],
              'truncation': 'min(C,4); an unseen mask means C>=4, not necessarily C=4',
              'input_masks': list(enumeration['inputs']),
              'source_sha256_lf': source_sha256_lf(),
              'source_hash_normalization': 'CRLF->LF then CR->LF; other bytes unchanged',
              'report_hash_encoding': HASH_ENCODING,
              'prefix_counts': enumeration['prefix_counts'],
              'ordinary_cost_counts': {str(k): sum(c == k for c in ordinary.values()) for k in range(4)},
              'c2_functions': fs, 'primary_nand_functions': gs,
              'pair_count': len(records), 'profile_class_count': len(classes),
              'good_signatures': good, 'bad_signatures': bad,
              'collisions': collisions, 'profile_classes': classes,
              'pair_records': records,
              'ordinary_records': [{'mask': f, 'cost': ordinary[f],
                                    'witness': enumeration['ordinary_witnesses'][f]}
                                   for f in sorted(ordinary)],
              'global_argument': [
                  'For combined essential support<=3, input deletion/padding preserves all costs and J; at least one input remains because g is nonconstant.',
                  'All C2 combined-support4/5 types have C(NAND(f,g))=4 by the separate six-case theorem, whereas J=2 implies that scalar cost<=3.',
                  'Hence membership in these five good truncated signatures decides J=2 for C(f)=2 once the ordinary compression and six-case premises are supplied; no end-to-end Lean refinement is claimed.']}
    report['report_sha256'] = report_digest(report)
    return report

def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true', help='write only the fixed project report')
    args = parser.parse_args(argv)
    report = build_report()
    if args.write:
        REPORT_PATH.parent.mkdir(exist_ok=True)
        REPORT_PATH.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8', newline='\n')
    print(json.dumps({'pairs': report['pair_count'], 'profiles': report['profile_class_count'],
                      'good_signatures': len(report['good_signatures']),
                      'bad_signatures': len(report['bad_signatures']),
                      'collisions': len(report['collisions']),
                      'source_sha256_lf': report['source_sha256_lf'],
                      'report_sha256': report['report_sha256']}, sort_keys=True))
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
