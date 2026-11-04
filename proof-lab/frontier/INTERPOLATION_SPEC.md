# Specification: NAND interpolation of finitely many labeled samples

Status: **mathematical construction and cost proof; not yet a Lean-checked theorem.** This note specifies the proposed implementation and its exact scope. It does not claim P != NP, exclude general succinct proofs, or prove that a particular target function is easy globally.

## 1. Model and theorem

Fix n >= 1. A circuit starts with the n input wires x_0,...,x_(n-1). Every appended gate is a binary NAND whose two predecessor indices refer to inputs or earlier gates. Repeating the same predecessor is permitted. Fanout and sharing are unrestricted. The output may be any input or computed wire, and unused gates are permitted (or may be pruned without increasing size). Size is the number of NAND gates. There are no free constants or free complemented input wires.

Input samples are a finite list

    S = [(a_0,b_0),...,(a_(m-1),b_(m-1))],

where every a_r is an n-bit assignment and every b_r is Boolean. Assume consistency:

    a_r = a_t implies b_r = b_t.

Let p be the number of positively labeled sample occurrences. Duplicates are allowed; thus p <= m. An implementation may deduplicate consistent samples, which can only lower the gate count.

**Interpolation theorem.** There exists a well-formed circuit C agreeing with every sample and having at most

    B(n,m) = 3 + n + (2*n + 1)*m

NAND gates.

A more precise count for the construction below is:

    p = 0:  exactly 3 emitted gates;
    p >= 1: exactly n + 2*p*(n-1) + 3*(p-1)
                   = n + (2*n+1)*p - 3 emitted gates.

These are construction counts, not minimum circuit-size claims. The second branch is used only for p>=1, so no negative or truncated-natural subtraction is being assumed.

## 2. Explicit primitive gadgets

An `emit(a,b)` operation appends NAND of the two existing wire indices and returns the new wire's index. If q wires currently exist, its arguments must be in [0,q), and the returned index is q.

### NOT: one gate

    u = emit(a,a)

For every assignment, u = not a. The repeated fan-in is legal.

### AND: two gates

    t = emit(a,b)
    u = emit(t,t)

For every assignment, t = not(a and b), and u = a and b. Both new gates refer only to available wires. The output is u.

### OR: three gates

    u = emit(a,a)
    v = emit(b,b)
    w = emit(u,v)

For every assignment, w = not((not a) and (not b)) = a or b. No complemented wire is treated as free.

### Constant zero: three gates, using n>=1

Starting from input wire x_0:

    u = emit(x_0,x_0)
    v = emit(u,x_0)
    z = emit(v,v)

Then u=not x_0, v=1, and z=0 on every assignment. With initial wire count n, the gate list is

    [(0,0), (n,0), (n+1,n+1)]

and the output index is n+2. This proves an upper bound of three gates; no minimality claim is needed.

## 3. Construction

### Branch p=0

Emit only the constant-zero gadget and choose its output. Every sample label is false, so all samples are matched. This branch covers an empty sample list as well as a nonempty all-negative list. It does not assume an empty OR is a free constant.

### Branch p>=1

1. Emit NOT(x_i) for all n input variables. These n complemented wires are shared by every subsequent minterm. Computing an unused negation is allowed and is included in the count.
2. For each positively labeled sample occurrence a, choose n existing literal wires: use x_i if a_i=1, and the computed NOT(x_i) otherwise.
3. Form the full minterm for a. Start with its first literal and combine the remaining n-1 literals using the two-gate AND gadget. This emits exactly 2(n-1) gates. For n=1 the minterm is simply its one literal, with no AND gates; no empty-conjunction convention is needed.
4. Store each of the p resulting minterm output wires.
5. Start with the first minterm output and OR in the remaining p-1 minterms using the three-gate OR gadget. This emits exactly 3(p-1) gates. For p=1 the output is already the minterm wire; no OR gate is added.

Every gate is appended using existing indices. Input-negation sharing and reuse of all earlier signals are legal. The algorithm therefore produces a well-formed topological circuit.

## 4. Agreement proof

For a positive assignment a, its minterm is true exactly when all n input bits equal a. On every Boolean assignment y,

    minterm_a(y) = true iff y = a.

This follows from the chosen positive/negative literal for each coordinate and the correctness of the AND gadget. The circuit in the p>=1 branch computes the disjunction of these full minterms.

- If (a,true) is a sample, the minterm for that occurrence is included, so the output at a is true.
- If (b,false) is a sample, consistency ensures that b equals no positively labeled sample assignment. Every included minterm is therefore false at b, so the output is false.
- Repeated positive samples merely repeat a disjunct, which does not change the Boolean function. Repeated negative samples add no disjunct. Consistent duplicates are harmless.
- An inconsistent duplicate pair with opposite labels admits no interpolating Boolean function at all. Such data violate the theorem's precondition and must be rejected; the construction must not claim to verify them.

The output on assignments not represented among the samples is unconstrained by interpolation. This particular construction returns true exactly on the sampled positive assignments and false elsewhere.

## 5. Gate-count proof and edge cases

For p>=1, the construction emits n negation gates, 2*p*(n-1) minterm gates, and 3*(p-1) disjunction gates. Hence

    g = n + (2*n+1)*p - 3
      <= n + (2*n+1)*m - 3
      <= 3 + n + (2*n+1)*m = B(n,m).

For p=0 it emits g=3 <= B(n,m), since n>=1 and m>=0.

Important edge cases:

- **m=0:** p=0. The constant-zero circuit is a valid witness; agreement is vacuous. The loose B(n,0)=3+n upper bound is valid.
- **All labels negative:** again p=0; three gates suffice regardless of m.
- **n=1, p=1:** the positive branch emits one input negation and no AND or OR gates. If the positive sample is input 1, the output may be the original input wire and the negation can be unused. If it is input 0, the output is the computed negation. Both are legal and within the stated count.
- **n=1 with repeated positives or both positive assignments:** the same OR construction remains correct; the count is deliberately loose and may include duplicate or redundant gates.
- **Full domain sampled:** the DNF construction is still valid with m=2^n, giving an ordinary exponential-size upper bound. This is consistent with counting lower bounds.
- **n=0:** excluded. With no input wires and no free constants, the three-gate constant gadget is unavailable. A separate zero-input convention would require a separate theorem.

Nothing here proves the bound optimal. Reusing more intermediate signals, omitting unused negations, or deduplicating samples may give smaller circuits.

## 6. Implementation obligations

An implementation should:

1. Validate n>=1, every assignment length n, Boolean labels, and duplicate-label consistency.
2. Use only NAND emit operations with exact in-range predecessor indices; reject malformed indices and Boolean/float values used as integer indices if the language permits such coercions.
3. Track actual emitted gate count and the output wire, rather than infer count from an unchecked certificate field.
4. Independently evaluate the returned circuit at every supplied assignment and compare with the supplied labels.
5. Check actual count <=B(n,m), including empty/all-negative lists and duplicate samples.
6. Distinguish a checked finite implementation test from the general theorem: tests alone do not prove this construction correct for all n,m.

The construction performs O(n+mn) gate-building work after consistency validation. Even a simple pairwise consistency check is polynomial in the explicit sample-list size. This is an efficiency statement in the size of the supplied data; it does not magically provide the unknown labels of an implicitly specified function.

## 7. Consequence for distinguishing sets

For a total Boolean target T on n bits, a set A is a distinguishing set against size <=s circuits when

    for every well-formed circuit C with at most s gates,
    there exists a in A with C(a) != T(a).

Assigning labels T(a) makes the sample data consistent automatically. The interpolation theorem gives a circuit agreeing with every point in A of size at most B(n,|A|). Therefore:

    if B(n,|A|) <= s, A cannot be such a distinguishing set.

Equivalently, every distinguishing set must satisfy the necessary (not sufficient) condition

    3+n+(2*n+1)*|A| > s.

This is a constructive obstruction. It does not rely on any cryptographic assumption or complexity-class separation.

## 8. Exact asymptotic statement

Suppose |A_n| <= C*n^d for all sufficiently large n, with fixed C>=0 and fixed integer d>=0. For n>=1,

    B(n,|A_n|) <= (4+3*C)*n^(d+1).

Here 3+n<=4*n<=4*n^(d+1), and (2*n+1)*C*n^d<=3*C*n^(d+1).

Assume s eventually dominates every polynomial with its constant factor: for every D>=0 and K>0 there is N such that s(n)>=K*n^D for all n>=N. Then eventually

    s(n) >= (4+3*C)*n^(d+1) >= B(n,|A_n|).

No polynomial-size family A_n can consequently distinguish its target T_n from every size <=s(n) circuit at all sufficiently large lengths. In particular, s(n)=n^k(n) with k(n) tending to infinity has this eventual-domination property.

If 'superpolynomial' means only that s is not O(n^D) for any fixed D, without eventual domination, the guaranteed conclusion is weaker: for each fixed polynomial bound on |A_n|, arbitrarily large lengths have s(n)>=(4+3*C)*n^(d+1), so the distinguishing property fails at arbitrarily large lengths. The note must not silently replace this with an eventual statement.

For a fixed exponent s=n^k, the theorem gives only the displayed necessary sample-size bound. It does not rule out every polynomial-size distinguishing set: the exponent of its sample bound matters.

## 9. Limits of the conclusion

This rules out polynomially many literal labeled samples as a universal distinguishing set against an eventually superpolynomial circuit-size budget. It applies even if A_n depends on the target: the interpolating circuit is allowed to depend on the samples and labels, and the distinguishing-set condition quantifies over all circuits of the allowed size.

It does **not** show that T_n is easy on unsampled inputs, exclude compressed or algebraic proof certificates, exclude other NP verifiers, or settle P versus NP. A richer certificate can contain structure beyond these labels and would need its own separate soundness, completeness, and length analysis.