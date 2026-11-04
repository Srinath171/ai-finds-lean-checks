# OR-chain extension variables give a short sparse certificate

This explicit example shows why the sparse Nullstellensatz lower bound for the
wide-clause family cannot be carried unchanged into a 3-CNF encoding with
extension variables. Here “3-CNF” means clauses of width **at most** three,
including the unit clauses. It is not a general proof-system simulation result.

## Formula and exact projection

Start with the unsatisfiable family

    (x_1 or ... or x_n) and (not x_1) and ... and (not x_n).

For n>=2 introduce y_2,...,y_n. Let a_2=x_1 and a_i=y_(i-1) for i>=3.
For each i=2,...,n include

    (not a_i or y_i),
    (not x_i or y_i),
    (a_i or x_i or not y_i).

Also include every negative unit `not x_i` and the positive unit `y_n`.
The three local clauses hold exactly when `y_i = (a_i or x_i)`. Induction
therefore gives a unique extension to every assignment of the x variables:
`y_i = OR(x_1,...,x_i)`. Existentially quantifying the y variables from the
chain and final positive unit yields the original wide disjunction. Adding
the negative units makes both formulations unsatisfiable. For n=1 the
construction is simply the two unit clauses `not x_1` and `x_1`.

DIMACS indices in the implementation are `x_i=i`, `y_i=n+i-1`. Clause order is
the three gate clauses for increasing i, then the negative x units, then the
final positive unit. Every literal occurrence is explicit.

## Formal sparse certificate

Use the clause-polynomial convention from `sparse_ns`: a positive literal x
contributes `(1-x)` and a negative literal contributes x. The third gate
clause consequently has polynomial

    F_i = (1-a_i)(1-x_i)y_i.

Let `B_i = product_(k=i..n) y_k`. Choose coefficients

    q_(F_i)        = product_(k=i+1..n) y_k,
    q_(not x_1)    = B_2,
    q_(not x_i)    = (1-a_i) B_i,                  i>=2,
    q_(y_n)        = 1.

All other clause coefficients and every Boolean-axiom coefficient r are zero.
Empty products are one. The `(1-a_i)B_i` coefficient is supplied as two
explicit monomial records, with coefficients +1 and -1. No arithmetic-circuit
coefficient representation is passed to the sparse verifier.

The identity is exact over the rational polynomial ring, without quotienting
by the Boolean axioms. For every i>=2, the third-clause term and the negative
x_i unit term add to

    (1-a_i)(1-x_i)B_i + (1-a_i)x_i B_i = (1-a_i)B_i.

Adding the x_1 unit term makes the i=2 expression equal B_2. For i>=3,

    (1-y_(i-1))B_i = B_i-B_(i-1).

The sum telescopes to y_n. The final positive unit contributes `1-y_n`, so
the entire sum is one. At n=1 the identity is `x_1+(1-x_1)=1`.

## Size and the encoding distinction

The exact counts, including the n=1 case, are:

| Quantity | Count |
| --- | ---: |
| Variables | 2n-1 |
| Clauses | 4n-2 |
| Literal occurrences | 8n-6 |
| Nonzero coefficient monomial records | 3n-1 |
| Entries in the supplied dense exponent vectors | (3n-1)(2n-1) |

The records consist of n-1 third-clause monomials, one x_1-unit monomial,
2(n-1) other negative-unit monomials, and one final-unit monomial. All
coefficients are +1 or -1 and all monomial exponents are zero or one.

The certificate has a linear **number of monomial records**. Its explicit
dense exponent vectors have Theta(n^2) entries, so this is not a claim of
linear encoded bit length. The input clause indices also require their
ordinary binary representation. The sparse lower bound on the original
wide-clause family uses different variables and generators; this construction
exhibits a polynomial-sized sparse certificate after that encoding changes.
It makes no statement about all 3-CNF formulas, arbitrary proof simulations,
polynomial proof-size bounds in general, NP versus coNP, or P versus NP.

## Bounded implementation and recorded evidence

`make_certificate(n)` accepts exact Python integers 1 through 16 and returns
the actual `nvars`, `clauses`, `q_coeffs`, and `r_coeffs` data accepted by the
existing `sparse_ns.verify_certificate`. Booleans, floats, strings, and values
outside the interval are rejected. `verify_case(n)` reports `MALFORMED` for
those inputs and otherwise calls the existing verifier without changing its
limits. This module has no model calls, credentials, ledger access, or
submitted-code execution.

The saved report records the bounded run for every n=1,...,16:

- n=1,...,10: `VALID` by the exact coefficient-span verifier.
- n=11,...,16: `RESOURCE_LIMIT` because 3n-1 exceeds the existing 31-record
  compiler cap. This is a refusal, not an invalid-certificate verdict. The
  mathematical telescoping argument still applies; the implementation does
  not raise its cap to complete these cases.
- n=10: 19 variables, 38 clauses, 74 literal occurrences, 29 records, and
  49,863 exact checker operations. The report includes its full certificate.
- All eight local OR assignments are checked independently. For n=1,...,6,
  exhaustive full Boolean assignments establish unique prefix-OR extensions,
  the existential projection, and absence of satisfying assignments after
  adding the units.
- For n=1,...,6, a separate expansion of the **original literal polynomials**
  gives zero formal residual. This calculation does not use the compiled
  diagonal factors or span elimination. Larger expansion/truth requests are
  rejected by the explicit n<=6 cap.

Tests also alter a coefficient and require `INVALID_NONZERO` with a witness
checked against the independently expanded original residual and the original
certificate coefficient formula. Tests compare every count, strict input
handling, the n=1/n=2 explicit encodings, and the cap refusals.

Run from `proof-lab`:

```powershell
.\.venv\Scripts\python.exe -B -m frontier.tseitin_certificate --write
.\.venv\Scripts\python.exe -B -m unittest tests.test_tseitin_certificate -v
```

The only result path written by `--write` is
`frontier/results/tseitin-certificate.json`. It is deterministic and includes
`source_sha256_lf`: SHA-256 of module bytes after CRLF becomes LF, then CR
becomes LF. All other bytes remain unchanged. Its `report_sha256` hashes the
report with that field omitted, serialized as UTF-8 JSON with sorted keys,
comma/colon separators, and `ensure_ascii=True`. These digests are independent
of checkout/report formatting line endings; they are integrity checks, not
proofs of mathematical correctness. The tests regenerate complete reports
from temporary LF, CRLF, and CR source copies without changing the real source.
