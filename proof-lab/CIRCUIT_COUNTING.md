# Circuit-description counting for general `n` and `k`

Research note for [`CircuitCounting.lean`](CircuitCounting.lean) (Lean 4.35.0,
core library only, no imports). This note records exactly what is proved,
with all quantifiers, what it does not prove, and the remaining gaps.

**No P versus NP claim is made anywhere in this work.**

## The model

For input count `n` and gate count `k` (both arbitrary natural numbers):

- Signals `0, …, n - 1` are the `n` inputs. There are no free constants and
  no free complemented inputs.
- The only gate type is binary NAND. A gate is described by an *ordered*
  fan-in pair; repetition is allowed (`NAND s s` is `NOT s`).
- Gate `i` (0-based) may use as fan-ins any of the `n + i` signals available
  before it: the `n` inputs plus the outputs of the previous `i` gates.
  This is topological order with unrestricted sharing (fanout is free,
  later gates see every earlier signal).
- A *description* of size `k` is a pair `(seq, out)`: a gate sequence
  `seq` of length `k` that is well-formed in the above sense, together with
  an output index `out < n + k` (the output may be an input or any gate
  output). Size means gate count.

In the Lean file, `gateSeqsN n k` enumerates all gate sequences,
`circuitsN n k` all descriptions of size exactly `k`, and
`circuitsUpToN n s` all descriptions of size at most `s`.

## What is proved

### Enumeration = independent well-formedness predicate

`WellFormedGatesN n seq` says every gate at index `i` in `seq` has both
fan-ins `< n + i`. The enumeration is proved to contain exactly these
sequences (`gateSeqsN_iff`, `circuitsN_iff`):

```lean
∀ n k (seq : List (Nat × Nat)),
  seq ∈ gateSeqsN n k ↔ seq.length = k ∧ WellFormedGatesN n seq

∀ n k (seq : List (Nat × Nat)) (out : Nat),
  (seq, out) ∈ circuitsN n k ↔
    seq.length = k ∧ WellFormedCircuitN n seq out
```

### Exact description count

`prodCount n k` is the product `∏_{i<k} (n + i)^2` defined recursively
(`prodCount n 0 = 1`, `prodCount n (k+1) = prodCount n k * (n + k)^2`).
The headline theorem (`circuitsN_count_exact`) is, for **all** `n, k`
(in particular all `n ≥ 1`):

```lean
∀ n k, (circuitsN n k).Nodup
     ∧ (circuitsN n k).length = (n + k) * ∏_{i<k} (n + i)^2
```

The `Nodup` conjunct matters: the list length is the number of *distinct*
descriptions, not a count with multiplicity. The factors have direct
meaning: gate `i` has `(n + i)^2` ordered fan-in choices, and the output
has `n + k` choices. For size at most `s` the exact count is the finite
sum (`circuitsUpToN_count_exact`):

```lean
∀ n s, (circuitsUpToN n s).Nodup
     ∧ (circuitsUpToN n s).length
         = ∑_{k ≤ s} (n + k) * ∏_{i<k} (n + i)^2     -- `descCountUpTo n s`
```

### Upper bound for size at most `s`

For `1 ≤ n` (theorem `circuitsUpToN_length_le`):

```lean
∀ n s, 1 ≤ n →
  (circuitsUpToN n s).length ≤ (s + 1) * (n + s) ^ (2 * s + 1)
```

Derivation, all formalised: each factor `(n + i)^2` with `i < k ≤ s` is at
most `(n + s)^2`, so `∏_{i<k} (n + i)^2 ≤ (n + s)^(2k)`
(`prodCount_le_pow`); multiplying by the output factor gives
`(n + k) * ∏_{i<k} (n + i)^2 ≤ (n + s)^(2s + 1)` (`descCount_le`); the sum
over the `s + 1` size classes `k = 0, …, s` is at most `s + 1` copies of
that bound (`descCountUpTo_le`, via the exact sum above).

### Pigeonhole: a missing truth table

Pure finite-list pigeonhole (`exists_missing_of_length_lt`), for every
type with decidable equality and **all** lists `all`, `computed`:

```lean
∀ (all computed : List α), all.Nodup →
  computed.length < all.length →
  ∃ t, t ∈ all ∧ t ∉ computed
```

Instantiated with `all = List.range (2^(2^n))` — the `2^(2^n)` truth-table
masks on `n` inputs — and `computed` the image of the descriptions under
any evaluation map (`exists_uncomputed_mask`, and
`exists_uncomputed_function` for the concrete NAND mask evaluation
`evalCircuitN` defined in the file):

```lean
∀ n s, 1 ≤ n → ∀ (eval : Description → Nat),
  (s + 1) * (n + s) ^ (2 * s + 1) < 2 ^ (2 ^ n) →
  ∃ mask, mask < 2 ^ (2 ^ n) ∧ ∀ c ∈ circuitsUpToN n s, eval c ≠ mask
```

Read literally: *if* the arithmetic hypothesis holds for a given `n, s`,
*then there exists* a truth table computed by no description of size
`≤ s`. One checked instance (kernel `decide` in the Lean file):
`n = 5, s = 3`, where `(3+1) * 8^7 = 8,388,608 < 2^32 = 4,294,967,296`,
so some 5-input Boolean function needs more than 3 NAND gates.

Sanity checks in the file reproduce the `n = 2` counts of
`CircuitBounds.lean` from the general definitions: sizes `0, 1, 2, 3`
have `2, 12, 144, 2880` descriptions, `3038` in total; also
`inputMask 2 0 = 10`, `inputMask 2 1 = 12`, and the 4-gate XOR witness
evaluates to mask `6`, all by kernel computation (`rfl`).

### Verification

- `lean CircuitCounting.lean` (Lean 4.35.0) compiles with no errors.
- No `sorry`, `admit`, `axiom`, or `native_decide` occurs in the file.
  (`decide` is used only for two concrete numeral inequalities.)
- `#print axioms` output for the main theorems — only Lean's standard
  axioms, no `sorryAx`:

```text
'gateSeqsN_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'circuitsN_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'circuitsN_count_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'circuitsUpToN_count_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'circuitsUpToN_length_le' depends on axioms: [propext, Quot.sound]
'exists_missing_of_length_lt' depends on axioms: [propext, Quot.sound]
'exists_uncomputed_mask' depends on axioms: [propext, Classical.choice, Quot.sound]
'exists_uncomputed_function' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## What this does not prove — read carefully

1. **A hard truth table is not an explicit hard function, and neither is
   an NP language.** The pigeonhole corollary is purely existential and
   non-constructive: it proves *some* mask is missed, without exhibiting
   one, giving an algorithm to find one, or giving a uniform family of
   functions (one per `n`) with any effectiveness property. An NP
   language requires a single uniform decision problem with a
   polynomial-time verifier; a per-`n` existence statement about
   anonymous truth tables provides none of that. Counting arguments of
   this shape (Shannon-style) show that *most* functions are hard, which
   alone gives no lower bound for any specified NP language.
2. **No nonmembership follows from a slow known algorithm.** Nothing here
   — and nothing about brute force or any other particular algorithm
   being slow — shows that a specific problem (e.g. SAT) is outside P or
   outside small circuits. A faster algorithm or a smaller circuit
   family might exist unknown; excluding that is precisely the hard
   content of lower-bound research, and it is not attempted here.
3. **No statement about P, NP, uniformity, or P/poly is formalised or
   claimed.** Bridging from circuit lower bounds to P vs NP would
   additionally need an *explicit* function in NP with a super-polynomial
   circuit lower bound. This work has neither ingredient.

## Remaining gaps (honest)

- **Asymptotics are not formalised.** The Lean corollary keeps the
  hypothesis `(s + 1) * (n + s)^(2*s + 1) < 2^(2^n)` explicit. The usual
  reading — that the hypothesis holds for `s` up to roughly
  `2^n / (2n)`, so most `n`-input functions need `Ω(2^n / n)` gates — is
  standard calculus but is *not* proved in Lean here; only concrete
  instances are machine-checked.
- **Semantics of `evalCircuitN` is checked by example, not by a general
  correctness theorem.** There is no Lean proof that `evalCircuitN`
  agrees with pointwise Boolean NAND evaluation on all assignments, nor a
  formal bijection between masks `< 2^(2^n)` and Boolean functions; that
  identification is the conventional one (bit `j` of the mask is the
  output on assignment `j`, bit `i` of `j` being input `i`), spot-checked
  at `n = 2` against `CircuitBounds.lean`. The counting and pigeonhole
  results themselves are evaluation-independent (`exists_uncomputed_mask`
  quantifies over all `eval`).
- **The bound is crude.** `(s + 1) * (n + s)^(2*s + 1)` over-counts (e.g.
  every factor is replaced by the largest one); it is a clean explicit
  bound, not a tight one.
- **Model fixed to one gate type.** Descriptions carry no gate-type
  choice, matching the NAND-only model. Allowing `g` gate types would
  multiply the exact count by `g^k`; the method is unchanged, but that
  variant is not formalised.
- The exact-count theorems are proved for all `n` including `0`; the
  `1 ≤ n` hypothesis is needed only for the upper-bound step (power
  monotonicity at base `n + s`).
