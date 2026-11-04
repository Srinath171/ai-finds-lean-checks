"""Recover semantic NAND factors for a fixed, labeled variable partition.

The input is a complete flat Boolean truth table in lexicographic variable order
(the first variable is the most significant bit).  The distinguished coordinate
z and ordered, disjoint, nonempty groups X and Y must partition that order.

For each b, nonempty rectangular zero support of F(b, X, Y) uniquely determines
A_b(X) and B_b(Y), with F = NAND(A, B).  This module verifies that semantic
factorization.  It does NOT recognize strict read-once NAND syntax, extract an
internal circuit node, handle singleton branches, or reconstruct a circuit.

Time is O(N) indexed table operations and auxiliary space is O(2^|X|+2^|Y|),
excluding the input table.  Bit/index arithmetic uses O(log N)-bit words.
"""

from collections.abc import Sequence
from dataclasses import dataclass
from typing import Literal


Status = Literal["RECOVERED", "EMPTY_RECTANGLE", "NOT_RECTANGLE"]
Cofactors = tuple[tuple[int, ...], tuple[int, ...]]


@dataclass(frozen=True)
class RecoveryResult:
    """For success, cofactor index b selects the table with z=b.

    Each A row follows x_variables order; each B row follows y_variables order.
    For failure, no factor tables are returned.  failure_z is the failing slice;
    a NOT_RECTANGLE witness is an assignment in variables order where both
    projected supports are 1 but the supplied F value is 1.  verified refers
    only to the complete semantic NAND factorization, never to NAND syntax.
    """

    status: Status
    verified: bool
    variables: tuple[str, ...]
    z: str
    x_variables: tuple[str, ...]
    y_variables: tuple[str, ...]
    a_cofactors: Cofactors | None = None
    b_cofactors: Cofactors | None = None
    failure_z: int | None = None
    witness: tuple[int, ...] | None = None


def _labels(value: Sequence[str], name: str) -> tuple[str, ...]:
    if isinstance(value, (str, bytes, bytearray)) or not isinstance(value, Sequence):
        raise TypeError(f"{name} must be an ordered sequence of labels")
    labels = tuple(value)
    if any(type(label) is not str for label in labels):
        raise TypeError(f"{name} labels must be strings")
    if any(not label for label in labels):
        raise ValueError(f"{name} labels must be nonempty")
    if len(set(labels)) != len(labels):
        raise ValueError(f"{name} labels must be distinct")
    return labels


def _offsets(group: tuple[str, ...], weights: dict[str, int]) -> list[int]:
    """Scatter lexicographic group indices into the input table's bit positions."""
    offsets = [0]
    for label in group:
        weight = weights[label]
        offsets = [next_offset for offset in offsets
                   for next_offset in (offset, offset | weight)]
    return offsets


def recover_rectangle(
    table: Sequence[int | bool], *, variables: Sequence[str], z: str,
    x: Sequence[str], y: Sequence[str],
) -> RecoveryResult:
    """Recover both cofactor pairs, or explain failure of the rectangle premise.

    Only exact bool values or exact ints 0/1 are accepted as table entries.
    Malformed argument types raise TypeError; invalid labels, dimensions, or
    values raise ValueError.  X and Y must both be nonempty.  EMPTY_RECTANGLE
    means a fixed-z zero set is empty, so the projection argument cannot recover
    both factors uniquely.  It does not mean no NAND factorization exists.
    NOT_RECTANGLE certifies that the specified partition admits no semantic
    NAND factorization.  If both kinds occur, the first failing slice is returned.
    """
    variable_order = _labels(variables, "variables")
    x_order = _labels(x, "x")
    y_order = _labels(y, "y")
    if type(z) is not str:
        raise TypeError("z must be a string label")
    if not z:
        raise ValueError("z must be nonempty")
    if not x_order or not y_order:
        raise ValueError("x and y must both be nonempty; singleton branches are outside this API")
    if z in x_order or z in y_order or set(x_order).intersection(y_order):
        raise ValueError("z, x, and y must be disjoint")
    if set(variable_order) != {z, *x_order, *y_order}:
        raise ValueError("z, x, and y must exactly partition variables")
    if isinstance(table, (str, bytes, bytearray)) or not isinstance(table, Sequence):
        raise TypeError("table must be an explicit ordered Boolean sequence")
    if len(table) != 1 << len(variable_order):
        raise ValueError("table length must be exactly 2**len(variables)")
    for value in table:
        if type(value) not in (bool, int):
            raise TypeError("table entries must be exact bools or ints")
        if value not in (0, 1):
            raise ValueError("table entries must be Boolean")

    weights = {label: 1 << (len(variable_order) - i - 1)
               for i, label in enumerate(variable_order)}
    x_offsets = _offsets(x_order, weights)
    y_offsets = _offsets(y_order, weights)
    a_rows: list[tuple[int, ...]] = []
    b_rows: list[tuple[int, ...]] = []
    common = dict(variables=variable_order, z=z,
                  x_variables=x_order, y_variables=y_order)

    for fixed_z in (0, 1):
        z_offset = weights[z] if fixed_z else 0
        a = [0] * len(x_offsets)
        b = [0] * len(y_offsets)
        found_zero = False
        for xi, x_offset in enumerate(x_offsets):
            for yi, y_offset in enumerate(y_offsets):
                index = z_offset | x_offset | y_offset
                if table[index] == 0:
                    a[xi] = 1
                    b[yi] = 1
                    found_zero = True
        if not found_zero:
            return RecoveryResult("EMPTY_RECTANGLE", False, **common,
                                  failure_z=fixed_z)

        # This checks every input row, including both directions of factorization.
        for xi, x_offset in enumerate(x_offsets):
            for yi, y_offset in enumerate(y_offsets):
                index = z_offset | x_offset | y_offset
                if table[index] != 1 - a[xi] * b[yi]:
                    assignment = tuple(int(bool(index & weights[label]))
                                       for label in variable_order)
                    return RecoveryResult("NOT_RECTANGLE", False, **common,
                                          failure_z=fixed_z, witness=assignment)
        a_rows.append(tuple(a))
        b_rows.append(tuple(b))

    return RecoveryResult("RECOVERED", True, **common,
                          a_cofactors=(a_rows[0], a_rows[1]),
                          b_cofactors=(b_rows[0], b_rows[1]))