# Exact subset-zeta evaluation kernel

This module reconstructs a known truth-table evaluation component from Ryan
Williams' algorithms-to-lower-bounds work. It is not a new SAT algorithm or a
solution to P versus NP. No paid models or external services are used.

## Exact bounded contract

`subset_zeta(n, histogram)` takes exactly `2**n` natural integers and returns

```text
g[A] = sum(histogram[S] for S subset of A).
```

An integer mask's bit `i` denotes variable `i`. The table is in increasing
numeric mask order, so its lower and upper halves differ in the highest bit.
The recursion is:

```text
zeta([a]) = [a]
zeta(L ++ U) = let l = zeta(L), u = zeta(U)
               in l ++ zipWith(+, l, u).
```

This makes exactly `n * 2**(n-1)` scalar additions for `n > 0`, and zero for
`n = 0`. Input values have at most 128 bits; nonnegative sums have at most
`128 + n` bits. Counters record actual additions and the largest bit length
encountered in histogram/value arithmetic, excluding indices and counters.

`evaluate_positive_and_sym(n, supports, accept_counts)` histograms positive AND
supports, transforms the histogram, and applies an explicit symmetric top gate.
Each support is a list/tuple of variable indices. Repeated literals in one AND
collapse to the same mask; repeated gates preserve multiplicity. An empty AND
is true. The top gate accepts exactly the supplied counts of true bottom gates;
it is an explicit list, never an executable callback. Empty accepted counts give
constant false, and zero bottom gates still have count zero.

Fixed caps are `0 <= n <= 18`, 128 input-value bits, at most 4096 bottom gates,
at most `n` literal entries per gate, and at most `s+1` accepted-count entries
for `s` bottom gates (hence at most 4097).
Exact integers are required: booleans, floats, and integer subclasses are
refused. There is no parameter that increases these caps. Circuit histogram
increments, support-mask OR operations, validation predicates, and top-gate
membership checks are separately counted. `scalar_additions` counts only the
zeta merges; `total_scalar_additions` also includes histogram increments.
`MALFORMED` and `RESOURCE_LIMIT` results have `satisfiable: null`; neither is an
UNSAT verdict.

## Scope of the literature connection

Williams' **Theorem 1.3** assumes a circuit-family class C containing AC0 and
closed under composition. It gives an absolute `k > 0` such that SAT on
`n`-variable, `n**c`-size C-circuits in deterministic `O(2**n / n**k)` time for
**every fixed c** implies that `NTIME[2**n]` lacks polynomial-size C-circuits.
One numerical speedup, selected input families, or a single size exponent does
not meet those quantifiers. The consequent does not settle P versus NP.

The positive-AND/SYM kernel here follows the dynamic-programming proof of
**Evaluation Lemma 4.2**. Its subset histogram counts which AND supports are
contained in each assignment. The full ACC SAT algorithm additionally uses
controlled variable absorption and an ACC-to-SYM+ transformation; neither is
implemented here. In particular, `O(n * 2**n)` work to emit a full table does
**not** achieve `2**n / n**k` SAT time: writing all values already costs
Omega(`2**n`). Exact integer and bit-growth accounting remains necessary when
interpreting arithmetic-operation counts as machine time.

Including input handling and the explicit top-gate table, the kernel uses
`O((n+1) * 2**n + (n+1) * s)` integer/entry operations. This form includes
`n = 0`, where `s` empty AND gates still require Theta(`s+1`) work. The
`O(n * 2**n + n*s)` form assumes `n >= 1`. The accepted-count list is compiled
into a Boolean array of length `s+1`, so applying the top gate uses direct
array lookup rather than hashing or executable callbacks.

Primary sources:

- Ryan Williams, *Nonuniform ACC Circuit Lower Bounds*, Journal of the ACM
  61(1), Article 2, **January 2014**:
  <https://dl.acm.org/doi/10.1145/2559903>.
- Author-hosted journal manuscript, **Theorem 1.3 and Evaluation Lemma 4.2**:
  <https://people.csail.mit.edu/rrw/acc-lbs-journal-final.pdf>.
  Its running publication metadata is a placeholder; the journal DOI above
  establishes the publication date.
- An explicitly dated author version, **July 31, 2012**:
  <https://people.csail.mit.edu/rrw/acc-lbs.pdf>.

The companion `SubsetZeta.lean` development, maintained separately, formalizes
its own balanced-table recursion. `kernel_correct` proves exact subset sums;
`flatten_lookup_allBits` and `allValues_correct` prove the order and all-table
output interpretation. `allValues_addition_count` proves exactly
`n * 2**(n-1)` additions (`n = 0` gives zero). This count measures scalar
**weight additions in the transform**, excluding histogram construction,
counter bookkeeping, flattening, applying the top gate, and integer bit costs.
`allValues_histogram` covers positive-AND counts with duplicate and empty
supports, and `allValues_symmetric_output` applies an abstract top acceptance
function. Python accepts only explicit top-gate data, not callbacks. The Lean
model uses recursive bit vectors and balanced tables; equivalence with this
Python flat-list parser and implementation is not formally proved.

## Reproduce and check

Run from `proof-lab`:

```powershell
python -m frontier.subset_zeta --write-demo
python -m unittest tests.test_subset_zeta
```

The default demo uses 16 variables, 1024 seeded positive AND gates, and the
explicit top rule `count % 7 in (2, 5)`. The complete table has 65,536 entries
and uses 524,288 zeta scalar additions. The saved result contains vector hashes,
compact summaries, and independently evaluated sample rows; it omits full
vectors. Tests independently compare every row against exhaustive subset sums
and source-circuit evaluation for `n = 0..8`, and check strict types, constants,
duplicates, caps, exact operation counts, and maximum bit growth. Sample checks
at the larger demo size are explicitly distinguished from full-table oracle
checks at the smaller test sizes.

Source hashes normalize CRLF and CR to LF before SHA-256, preserving all other
bytes. Vector hashes use UTF-8 compact JSON with ASCII escaping and no trailing
newline. The demo is deterministic for the documented Python `random.Random`
generator and seed; the artifact is compared against a regenerated report in
the tests.
