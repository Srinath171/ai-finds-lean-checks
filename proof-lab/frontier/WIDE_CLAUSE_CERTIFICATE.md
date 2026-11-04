# A short factored certificate despite a large sparse expansion

[wide_clause_certificate.py](wide_clause_certificate.py) constructs one explicit
Nullstellensatz certificate for the easily unsatisfiable formula

```text
(x0 OR ... OR x_(n-1)) AND (NOT x0) AND ... AND (NOT x_(n-1)).
```

The wide-clause polynomial is `F_wide=product_i(1-x_i)` and each negative-unit
polynomial is `F_unit_i=x_i`. The supplied coefficients are `q_wide=1` and
`q_unit_i=product_(j<i)(1-x_j)` for `i=0,...,n-1`; all Boolean-axiom coefficients
are zero. Thus the exact formal rational-polynomial residual is

```text
product_i(1-x_i) + sum_i x_i*product_(j<i)(1-x_j) - 1 = 0.
```

To see the identity, write `P_i=product_(j<i)(1-x_j)`. Then
`P_i-P_(i+1)=P_i*x_i`, so summing gives `1-P_n`. This is a telescoping
identity over the rationals, not merely agreement on Boolean points.
For n=0 the formula contains an empty clause; the products are one and
the residual is `1-1`.

## Representation and observed result

The constructor writes a sum of products of explicitly sparse UNIVARIATE
factors. It never expands the multivariate coefficient polynomials.
It passes this data to the existing exact rational [diagonal identity
kernel](diagonal_pit.py), with its resource limits unchanged.

The residual has `n+2` summands, `n*(n+2)` factor slots, and
`(3*n*n+5*n)/2` nonzero factor entries. Each factor has at most two entries.
The displayed coefficient polynomials, if individually expanded into
monomial records, have counts `1,1,2,4,...,2^(n-1)`, total `2^n`.
These are counts of THIS presented prefix certificate. They do not by
themselves prove a lower bound for every certificate.

At n=24 the recorded run is:

| Quantity | Value |
|---|---:|
| Kernel status | VERIFIED_ZERO |
| Variables | 24 |
| Residual width | 26 |
| Factor slots | 624 |
| Sparse univariate factor entries | 924 |
| Expanded coefficient records of this prefix | 16,777,216 |
| Conservative operation preflight | 1,474,876 |
| Performed rational operations | 57,178 |
| Largest observed rational bit length | 1 |

The n=30 example is refused as `RESOURCE_LIMIT` by the existing operation
preflight. This is not a false or invalid proof verdict, and no limits
were raised. `selected_completed_n` reports the requested n=24 when it
finishes; the experiment would descend through smaller n only if that
requested run were refused. It does not claim that 24 is the greatest
arity that could fit.

[The saved report](results/wide-clause-certificate.json) records the fixed
kernel limits and LF-normalized source/kernel hashes. LF, CRLF and CR
checkouts give the same report.

## Independent checks and scope

Eleven focused tests passed. Separate original-literal polynomial
multiplication expands n=0,...,6 and verifies the zero residual and the
individual prefix counts. The tests also check all compiled factor-entry
counts, the n=24 run, exact source coefficients at small and binary-large
exponents, malformed inputs, resource refusals, and saved-report replay.
Deleting any unit summand at tested n=1,...,6 gives a formal nonzero
residual. Its kernel witness is independently checked both against the
original-expression coefficient formula and the small expansion.

The code is a tested explicit construction using an exact restricted
identity kernel, not a Lean refinement of either program. The independent
project theorem about ALL sparse certificates, if established, is a
separate result. This experiment illustrates why a sparse-format lower
bound need not apply to a richer factored format. It supplies neither a
general arithmetic-DAG identity test nor polynomial-size refutations for
all unsatisfiable formulas. There is no general computational hardness
in this easily refuted formula family, and no P versus NP conclusion.

From the proof-lab directory:

```powershell
.venv\Scripts\python.exe -B -m frontier.wide_clause_certificate --write
.venv\Scripts\python.exe -B -m unittest tests.test_wide_clause_certificate -v
```

Only the four assigned experiment, test, note and result files were
created. No model calls, network, credentials, ledger or live research
state were accessed; the existing kernel was not modified.
