# Quantifier and certificate audit of finite diagonalization

This is a mathematical audit of a proposed route, not a proof of P != NP or NP not contained in P/poly. The circuit model is topologically ordered binary NAND, with repetition and sharing allowed, no free constants or complemented inputs, and any input or computed signal selectable as output.

## Fixed exponent versus one language beating every polynomial

Fix an integer k >= 0. At each input length n >= 1, enumerate every circuit description of size at most n^k. If a truth table is missing, choose the first missing table in a fixed, explicitly specified ordering. Use a fixed fallback at lengths where no table is missing. Call the resulting table f_(k,n), and define L_k(x) = f_(k,|x|)(x).

The circuit-description bound and the number 2^(2^n) of n-input Boolean functions give the exact eventual statement:

    for every fixed k, there exists N_k such that for every n >= N_k,
    C_NAND(f_(k,n)) > n^k.

This excludes the one exact threshold n^k. It does not even exclude c*n^k for an arbitrary fixed c > 1, and certainly does not exclude n^(k+1). A family can exceed one threshold and still have polynomial-size circuits.

The single-language conclusion needed to exclude P/poly is instead of the form:

    there exists one L in NP such that for every degree d and constant c,
    at arbitrarily large lengths n, C_NAND(L_n) > c*n^d.

An eventual bound for every degree would suffice, but is stronger than necessary. The order of the quantifiers matters: a different L_k for each k is not one L beating all polynomial degrees. Even if every separate L_k had some NP verifier, those verifiers would still need an appropriate uniform construction and a single fixed polynomial bound to combine them into one NP language.

One can choose a slowly growing exponent and computationally specify one hard family by exhaustive diagonalization. That alone does not place the resulting language in NP. Conversely, a slow displayed construction does not prove that the language is outside NP: it gives no lower bound against every alternative algorithm or verifier.

## Size of the proposed explicit certificate

Let s = n^k. The number of ordered syntactic descriptions, including the output selector, is

    M(n,s) = sum_(j=0)^s (n+j) * product_(i=0)^(j-1) (n+i)^2.

The empty product at j=0 is one. Distinct descriptions may compute the same function; M is not a count of distinct functions.

A certificate containing a complete table T and one disagreement assignment a_C for each circuit description C uses approximately

    2^n + n*M(n,s)

bits before indexing and serialization overhead. Checking it must inspect every required description, evaluate its gates on a_C, and confirm T(a_C) differs from C(a_C). With random-access table lookup the gate work is O(M(n,s)*s), in addition to reading the certificate and any enumeration/indexing overhead. A sequential-machine implementation may incur further table-access overhead; that cannot rescue polynomial time in n.

For fixed k >= 1, log_2 M(n,n^k) = Theta(n^k log n), so this explicit representation is superpolynomial in the original input length n. For k=0 the complete truth table alone already has 2^n bits. Polynomial checking in the size of this long certificate is not the polynomial-in-n certificate bound required by NP.

Grouping descriptions with equal computed truth tables can shorten the disagreement list, but the verifier still needs sound evidence that the groups cover every allowed circuit. Compression is not an automatic NP-membership argument.

## Missing-table evidence is not lexicographic minimality

The disagreements above certify only that the submitted T is not computed by any circuit of size at most s. They do not certify that T is the first missing table, which is the definition used for L_k.

A direct minimality certificate would additionally show that every earlier truth table is computed by an allowed circuit. The rank of the first missing table is at most the number of distinct computed tables, hence at most M, but this is still potentially enormous. A certificate for an arbitrary missing table can therefore be insufficient even before considering the NP length bound.

Failure of these naive certificate formats proves neither that no compressed certificate exists nor that no different polynomial-time verifier exists. A genuine NP claim must supply one verifier and one polynomial witness bound valid for all inputs; the construction above does not supply them.

## Two finite tests with precise scope

### 1. Parity scaling through three inputs

Let P_n be the XOR of all n input bits. Test, only for n in {1,2,3},

    C_NAND(P_n) = 4*(n-1).

The expected costs are 0, 4, and 8. The first is an input wire. The two-input minimum has a separate Lean proof in this project. The three-input minimum is currently bounded solver evidence, with an independently checked eight-gate witness and solver UNSAT reports for budgets zero through seven; it is not a Lean lower-bound theorem.

Passing these three cases does not establish the displayed formula for all n, and parity is itself an efficiently computable family.

### 2. First missing need not mean hardest

Consider the falsifiable assertion that the first missing truth table always realizes the maximum circuit complexity at that input length.

At n=2 and s=0, the only available outputs are the two projections. The first missing table is constant zero. It has a circuit of at most three gates:

    u = NAND(x0,x0)
    v = NAND(u,x0)
    zero = NAND(v,v).

Thus its minimum is at most three. Two-input XOR requires at least four gates in the same model. Therefore the first missing table is not maximally hard. This counterexample does not depend on any XNOR minimum claim.

Lexicographic diagonalization guarantees exclusion of the chosen threshold when a missing table exists. It supplies no stronger hardness margin automatically.

## Remaining blocker

The missing step is a justified construction of one specified language with an NP verifier and the required asymptotic circuit lower bounds. Finite enumeration, long explicit disagreement lists, and failure of a particular verifier format do not provide that step.