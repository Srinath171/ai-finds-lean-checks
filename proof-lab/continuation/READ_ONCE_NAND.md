# Strict read-once NAND reconstruction

This is independently AI-reviewed ordinary mathematics with a bounded Python implementation; it is not an end-to-end Lean proof, a novelty claim, or a solution of P versus NP. The current implementation accepts at most five input variables and makes resource refusals explicit.

## Exact model and statement

A circuit starts with positive input wires only. Every paid gate is binary NAND, including equal fanins; output selection is free. Constants and NOT are not free. A strict read-once tree is a full binary NAND tree whose leaves are distinct positive inputs. Unused ambient inputs are allowed.

Given a complete Boolean truth table with `d >= 1` essential inputs, the algorithm decides whether such a tree exists and reconstructs one. This is equivalent to `C_NAND(f) = d-1`. Constants have no nonempty strict read-once tree and are rejected; this does not say their circuit costs are infinite. With at least one ambient input, constant one costs two NAND gates and constant zero costs three.

## Signed restrictions are sufficient states

For each partial assignment `rho` in `{0,1,*}^d`, consider both the restriction `f|rho` and its Boolean complement, with inessential free coordinates removed. There are at most `2*3^d` resulting semantic states, before deduplication can only reduce this count. A sign is bookkeeping for candidate functions; it does not provide a free output NOT gate.

Every subtree of an actual read-once tree is one of these states. At each ancestor, assign the disjoint sibling subtree an input on which it is one. Such an assignment exists: every positive-leaf read-once subtree attains both Boolean values, by induction. Then `NAND(a,1)=not a`; composing the ancestors exposes the desired subtree or its complement. Distinct sibling subtrees use disjoint variables, so all chosen assignments are simultaneously consistent.

The implementation discovers these states on demand, memoizing their canonical essential-coordinate tables. It need not generate the entire pool.

## The exact root test

Let `q` be a state with essential support `S`, and choose a nonempty proper partition `S=U disjoint_union V`. Select any zero `(u0,v0)` of `q`. Define

```
g(u) = 1-q(u,v0)
h(v) = 1-q(u0,v).
```

Test every entry of the exact identity

```
1-q(u,v) = g(u)*h(v).
```

If `q=NAND(g0(U),h0(V))`, the chosen zero forces `g0(u0)=h0(v0)=1`, so these extracted factors are exactly `g0,h0`. Conversely the displayed identity literally proves the required NAND decomposition. Because `q` depends essentially on every coordinate of `S`, a successful partition has two nonconstant factors depending on all of `U,V`.

Both extracted factors are complements of cofactors of `q`, hence are still signed restrictions of the original table. Recursively recognize them on strictly smaller supports. On one essential variable, accept only the positive projection; reject its complement. Reject every zero-essential state. A rectangle test alone is insufficient: the three-input NAND has a root rectangle but needs an AND child, which is not a one-gate NAND tree on its two inputs.

Soundness follows by joining the reconstructed child trees with an actual NAND gate. Completeness follows by trying the actual root partition and using the subtree-state argument. Commutativity permits considering only partitions with the first coordinate on the left.

## Why this is the optimal input-count boundary

A fanin-two circuit depending on `d` inputs needs at least `d-1` gates. Prune to the ancestor graph of its output, and count each gate-fanin occurrence as an edge, even for repeated fanins. If there are `k` gates and `ell >= d` distinct input vertices, the connected ancestor multigraph has `k+ell` vertices and `2k` edges, hence `2k >= k+ell-1`.

If `k=d-1`, equality forces `ell=d` and the connected multigraph is a tree: it has no parallel edges or shared ancestor. It is therefore a full binary read-once NAND tree. Conversely a strict tree on `d` leaves has exactly `d-1` gates. For `d=1`, only the positive projection has cost zero. This proves the claimed exact boundary; it does not solve reconstruction with a repeated leaf or a larger gate budget.

## Ordinary complexity bound

For a raw restriction with `k` free coordinates, exact canonicalization and table extraction cost a polynomial in `d` times `2^k`. All root partitions and their table scans cost a polynomial in `d` times `4^k`. Summing over the signed restriction pool gives

```
2 * sum_k binom(d,k) * 2^(d-k) * 4^k = 2*6^d.
```

Canonical keys can be sorted and searched deterministically; table comparison, coordinate bookkeeping, and logarithmic search factors change only polynomial factors in `d`. Thus a straightforward deterministic implementation has `poly(d)*6^d` time and `poly(d)*4^d` stored table bits/metadata after essential-input compression. Here `N=2^d` is the compressed truth-table length. If the original table has `n` ambient variables including dummies, finding and deleting them first costs `poly(n)*2^n`, and the overall algorithm is still polynomial in the original table length `2^n`. This ordinary asymptotic argument is independent of the fixed implementation cap and is not a claim of a faster-than-truth-table SAT algorithm.

## Bounded implementation and validation

`read_once_nand.py` provides `recognize(n, mask, limits=Limits())`. Bit `a` is the output on `x_i=(a>>i)&1`. Exact integer types are required; Boolean/float aliases are rejected. Default caps are five ambient variables, 512 memo states, and 1,000,000 charged target-table lookups. Only smaller caps are accepted. Statuses are `READ_ONCE`, `NOT_READ_ONCE`, `MALFORMED`, and `RESOURCE_LIMIT`; a refusal never asserts nonexistence. The lookup counter counts calls to the charged table accessor, not every CPU instruction or extracted-factor bit operation.

Successful outputs include an actual topological NAND gate list and output wire, preserving original ambient input indices. No constants or negative leaves are inserted. These are checked by independent Boolean-row simulation in the tests.

The nine focused tests exhaust **all Boolean functions through three ambient variables** and compare the accepted set with separately generated genuine NAND trees. They also enumerate **all full-support tree shapes through five variables**, obtaining distinct function counts `1,1,3,15,105`, and check trees on every nonempty support subset of five ambient variables. This is not exhaustive enumeration of all `2^32` Boolean functions on five variables. Constants, negative leaves, NAND3, and an essential four-variable nonunate repeated-`z` circuit are rejected. Strict metadata, caps, deterministic counters, source hash, and canonical report hash are checked.

Run from `proof-lab`:

```
.venv\Scripts\python.exe -B -m continuation.read_once_nand --write
.venv\Scripts\python.exe -B -m unittest continuation.test_read_once_nand -v
```

The fixed demonstration is `results/read-once-nand-demo.json`. Its canonical report hash excludes its own hash field, sorts JSON keys with compact ASCII encoding, and appends one LF. The source hash normalizes CRLF and CR to LF. The artifact records examples, caps, statuses, actual witnesses, and charged counters; it contains no model calls or credentials.
