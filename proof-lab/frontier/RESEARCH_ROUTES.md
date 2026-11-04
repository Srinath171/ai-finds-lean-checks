# Other research routes and the exact remaining gaps

## Algorithms to circuit lower bounds

The subset-zeta work reconstructs one standard all-values evaluation component, not a new SAT saving. [SUBSET_ZETA.md](SUBSET_ZETA.md) gives the exact hypotheses, implementation limits, formal statements, and link to [Williams's author manuscript](https://people.csail.mit.edu/rrw/acc-lbs-journal-final.pdf), Theorem 1.3 and Evaluation Lemma 4.2.

The remaining task is a proved uniform worst-case SAT saving for an eligible circuit class, including every required fixed polynomial size exponent and controlled representation transformations. Evaluating all assignments with O(n*2^n) weight additions does not itself meet that target: the output table already has 2^n entries. A finite timing improvement cannot substitute for the missing asymptotic theorem. No full algorithms-to-lower-bounds implication is formalized in this project.

## Proof complexity and certificate representation

[Grochow and Pitassi's 2014 paper](https://arxiv.org/abs/1404.3820) distinguishes arithmetic-circuit proof representations from monomial counts and relates its IPS lower bounds to algebraic circuit lower bounds. The current rational sparse-record theorem therefore cannot be transferred to arbitrary circuit-encoded coefficients.

This project now gives concrete counterpoints: the wide-clause family has a short factored prefix certificate, and its OR-chain 3-CNF encoding has a polynomial-sized sparse certificate. Neither supplies short certificates for all unsatisfiable formulas. See [the sparse bound](SPARSE_CERTIFICATE_BOUND.md), [factored witness](WIDE_CLAUSE_CERTIFICATE.md), and [extension-variable witness](TSEITIN_CERTIFICATE.md).

## A general boundary of the existing diagonal checker

The original coefficient-matrix argument below is self-contained. An equivalent Boolean-evaluation-matrix argument is now verified in [DiagonalWidth.lean](DiagonalWidth.lean), including the actual weighted factorization and a `4m+1`-node formula. The exact source statement and limits are in [DIAGONAL_WIDTH.md](DIAGONAL_WIDTH.md). No novelty is claimed. Work over Q in the ORIGINAL coordinates X=(x_1,...,x_m), Y=(y_1,...,y_m). Let

    H_m(X,Y) = product_i(x_i+y_i).

A binary arithmetic formula uses m additions and m-1 multiplications. Any representation as

    H_m = sum_(j=1)^W product_(v in X union Y) p_(j,v)(v)

requires W>=2^m. Form its squarefree coefficient matrix, with rows x_S and columns y_T. Expansion selects exactly one variable from each pair, so the matrix entry is one exactly when T is the complement of S. This is a 2^m-by-2^m permutation matrix, with rank 2^m. Each univariate-product summand gives an outer product across X|Y and has rank at most one. Matrix rank is subadditive, hence W>=2^m. Unrestricted univariate degrees do not help: the selected coefficient submatrix still has that outer-product decomposition.

Thus arbitrary small arithmetic formulas cannot always be compiled with polynomial width into this fixed-coordinate sum-of-univariate-products representation. This is a representation lower bound, not an impossibility theorem for general PIT, invertible variable changes, other preprocessing, or all proof certificates. The standard coefficient-matrix rank method is explained in [Raz, ECCC TR03-067 (2003), section 3](https://eccc.weizmann.ac.il/report/2003/067/download/).

The completed formalization uses the explicit inverse of [[0,1],[1,2]] and its tensor products. [FiniteDimension.lean](FiniteDimension.lean) proves the needed rectangular right-inverse dimension inequality by actual rational pivot elimination. Neither a general PIT algorithm nor a lower bound on all certificates follows. A future paid call needs a concrete new hypothesis to test, rather than repeating these established missing premises.
