"""Bounded exact synthesis of strict NAND trees with one repeated variable.

Ordinary inputs are x_0,...,x_(n-1); z is input bit n. A truth mask's bit a
is the output at assignment a. Each ordinary input occurs exactly once,
and z occurs exactly z_reads times (0,1,2). Constants and NOT are not free.

The solver preserves syntactic variable sets, including coordinates ignored
by a fixed cofactor. It never merges a specified demand with a wildcard.
This is a formula-class algorithm, not unrestricted DAG synthesis or P vs NP.
"""
from __future__ import annotations
from dataclasses import dataclass
import time


class ResourceLimit(Exception):
    pass


def _exact_int(value, low, high):
    return type(value) is int and low <= value <= high


def _fits_mask(value, bits):
    return type(value) is int and value >= 0 and value.bit_length() <= bits


@dataclass(frozen=True)
class Limits:
    seconds: float = 10.0
    max_states: int = 100000
    max_transitions: int = 1000000

    def valid(self):
        return (type(self.seconds) in (int, float) and 0 < self.seconds <= 60
                and _exact_int(self.max_states, 1, 1000000)
                and _exact_int(self.max_transitions, 1, 5000000))


class _Search:
    def __init__(self, n, limits, clock=None):
        self.n, self.limits = n, limits
        self.clock = clock or time.monotonic
        self.started = self.clock()
        self.deadline = self.started + limits.seconds
        self.states = self.transitions = self.memo_hits = 0
        self.memo = {}

    def _check(self):
        if self.clock() >= self.deadline:
            raise ResourceLimit('time_limit')

    def _factors(self, S, left, demand):
        """Return ALL sufficient child-demand pairs for a specified split."""
        if demand is None:
            return ((None, None),)
        coordinates = [i for i in range(self.n) if (S >> i) & 1]
        left_positions = [j for j, i in enumerate(coordinates) if (left >> i) & 1]
        right_positions = [j for j, i in enumerate(coordinates) if not ((left >> i) & 1)]
        zeros = 0
        left_projection = right_projection = 0
        for row in range(1 << len(coordinates)):
            if row % 64 == 0:
                self._check()
            if (demand >> row) & 1:
                continue
            zeros += 1
            lrow = sum(((row >> pos) & 1) << j for j, pos in enumerate(left_positions))
            rrow = sum(((row >> pos) & 1) << j for j, pos in enumerate(right_positions))
            left_projection |= 1 << lrow
            right_projection |= 1 << rrow
        if zeros == 0:
            return ((0, None), (None, 0))
        if zeros != left_projection.bit_count() * right_projection.bit_count():
            return ()
        return ((left_projection, right_projection),)

    def solve(self, S, k, demand0, demand1):
        self._check()
        key = (S, k, demand0, demand1)
        if key in self.memo:
            self.memo_hits += 1
            return self.memo[key]
        if self.states >= self.limits.max_states:
            raise ResourceLimit('state_limit')
        self.states += 1
        rank = S.bit_count() + k
        if rank < 1:
            self.memo[key] = None
            return None
        if rank == 1:
            if S == 0 and k == 1:
                tree, values = ('z',), (0, 1)
            elif S.bit_count() == 1 and k == 0:
                tree, values = ('x', S.bit_length()-1), (2, 2)
            else:
                tree, values = None, ()
            if tree is not None and all(d is None or d == v for d, v in zip((demand0, demand1), values)):
                self.memo[key] = tree
                return tree
            self.memo[key] = None
            return None
        left = S
        while True:
            right = S ^ left
            # Factors depend on the variable split, not the z allocation.
            options0 = self._factors(S, left, demand0)
            options1 = self._factors(S, left, demand1)
            if options0 and options1:
                for kl in range(k+1):
                    kr = k-kl
                    if left.bit_count()+kl < 1 or right.bit_count()+kr < 1:
                        continue
                    for l0, r0 in options0:
                        for l1, r1 in options1:
                            self._check()
                            if self.transitions >= self.limits.max_transitions:
                                raise ResourceLimit('transition_limit')
                            self.transitions += 1
                            lt = self.solve(left, kl, l0, l1)
                            if lt is None:
                                continue
                            rt = self.solve(right, kr, r0, r1)
                            if rt is not None:
                                tree = ('nand', lt, rt)
                                self.memo[key] = tree
                                return tree
            if left == 0:
                break
            left = (left-1) & S
        self.memo[key] = None
        return None


def evaluate_tree(tree, assignment, n):
    """Actual Boolean evaluation, independent of rectangle operations."""
    if tree[0] == 'x':
        return bool((assignment >> tree[1]) & 1)
    if tree[0] == 'z':
        return bool((assignment >> n) & 1)
    return not (evaluate_tree(tree[1], assignment, n) and evaluate_tree(tree[2], assignment, n))


def verify_tree(tree, mask, n, z_reads):
    """Check topology, exact positive leaves, gate count, and every input row."""
    if not _exact_int(n, 0, 12) or not _exact_int(z_reads, 0, 2):
        return False
    if not _fits_mask(mask, 1 << (n+1)) or n+z_reads < 1:
        return False
    counts, zs, gates, visited = [0]*n, 0, 0, 0
    pending = [tree]
    while pending:
        item = pending.pop()
        visited += 1
        if visited > 2*(n+z_reads)-1 or type(item) is not tuple or not item:
            return False
        if item[0] == 'x' and len(item) == 2 and _exact_int(item[1], 0, n-1):
            counts[item[1]] += 1
        elif item == ('z',):
            zs += 1
        elif item[0] == 'nand' and len(item) == 3:
            gates += 1
            pending.extend((item[1], item[2]))
        else:
            return False
    if counts != [1]*n or zs != z_reads or gates != n+z_reads-1:
        return False
    return all(evaluate_tree(tree, a, n) == bool((mask >> a) & 1) for a in range(1 << (n+1)))


def reconstruct(mask, n, *, z_reads=2, limits=None):
    """Return REPRESENTABLE, NOT_REPRESENTABLE, RESOURCE_LIMIT, or INVALID_INPUT.

    A negative verdict is exact only when search finishes. Resource limits
    never become a negative verdict. For z_reads=0 the table still includes
    the z coordinate; representability requires both slices to agree.
    """
    if limits is None:
        limits = Limits()
    if (not _exact_int(n, 0, 12) or not _exact_int(z_reads, 0, 2)
            or n+z_reads < 1 or not isinstance(limits, Limits) or not limits.valid()
            or not _fits_mask(mask, 1 << (n+1))):
        return {'status': 'INVALID_INPUT', 'tree': None, 'reason': 'invalid_dimensions_mask_or_limits'}
    width = 1 << n
    full = (1 << width)-1
    search = _Search(n, limits)
    try:
        tree = search.solve((1 << n)-1, z_reads, mask & full, mask >> width)
        if tree is not None and not verify_tree(tree, mask, n, z_reads):
            raise AssertionError('constructed witness failed independent row verification')
        result = {'status': 'REPRESENTABLE' if tree is not None else 'NOT_REPRESENTABLE',
                  'tree': tree, 'gate_count': n+z_reads-1 if tree is not None else None}
    except ResourceLimit as exc:
        result = {'status': 'RESOURCE_LIMIT', 'tree': None, 'reason': str(exc)}
    result.update(n=n, z_reads=z_reads, states=search.states,
                  transitions=search.transitions, memo_hits=search.memo_hits,
                  elapsed_seconds=round(time.monotonic()-search.started, 6))
    return result
