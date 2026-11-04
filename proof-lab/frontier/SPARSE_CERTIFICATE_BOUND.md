# All-certificates sparse Nullstellensatz record lower bound

`SparseCertificateBound.lean` proves the exponential sparse-record bound
for the wide positive clause together with all negative unit clauses:

```text
(x_0 OR ... OR x_(n-1)) AND NOT x_0 AND ... AND NOT x_(n-1).
```

This is a general result for every natural n, over actual rational
coefficients and arbitrary natural exponents. It is an all-certificates
bound for the stated explicit sparse coefficient format, stronger than
the earlier example in `CertificateBlowup.lean` about one inefficient
certificate. It is not a lower bound for arbitrary proof systems.

## Precise formal input and conclusion

A coefficient polynomial is a list of `(List Nat, Rat)` records. The
exponent-vector length is checked against n. Exponents need not be 0 or 1;
zeros, repeated exponents, and canceling coefficient records are allowed.
`nzCount p` is explicitly the length of p after filtering out records with
zero coefficient. Counts are taken separately in q0, each q_i, and each
r_i slot; like monomials in different slots are not globally merged.

`RationalCertificate n q0 qs rs D` requires n unit coefficients, n
Boolean-axiom coefficients, the proper exponent width in every slot, and
the following equality on **every rational input vector of length n**:

```text
q0(x) * product_i(1-x_i)
  + sum_i q_i(x)*x_i
  + sum_i r_i(x)*(x_i^2-x_i) = D.
```

Here all polynomial values are computed from the actual rational
coefficient records and ordinary natural powers. The wide-clause product
is represented as a product, not silently expanded and charged to the
coefficient lists.

For every nonzero rational D, `rational_certificate_bound` proves

```text
2^n <= nzCount(q0) + sum_i nzCount(q_i).
```

Thus arbitrary Boolean-axiom coefficients cannot evade the bound.
For D=1, `nullstellensatz_total_records_bound` also states the lower bound
including all r_i records in the total certificate count. No nonzero-input
coefficient hypothesis or no-duplicates hypothesis is needed. For
canonical sparse polynomial lists this is the usual sum of nonzero
monomial counts; for general lists it bounds the explicitly supplied
nonzero coefficient records.

## The actual certificate-to-support bridge

No support-cover condition is assumed. The proof derives it:

1. `SparseMonomial.lean` evaluates genuine natural exponent vectors and
   proves that collapsing every positive exponent to a squarefree support
   bit preserves Boolean evaluation and does not add records. It also
   proves agreement with ordinary rational monomial evaluation under the
   Boolean embedding, including arbitrary powers.
2. `rational_certificate_to_boolean` specializes the actual all-rational
   identity to Boolean inputs. The wide product becomes exactly the
   all-zero-row indicator; every x_i^2-x_i becomes zero. The resulting
   `BooleanCertificate` is an evaluated identity, not a claimed support
   cover or an assumed multilinear quotient equality.
3. The q_i*x_i contribution is represented by forcing support bit i to
   true. `forceAt_eval` and `unitTokensFrom_value` prove this matches the
   actual coefficient evaluations. `unitTokensFrom_nzCount` proves the
   number of nonzero records is preserved slot-by-slot.
4. From the certificate identity, the sum of those unit contributions is
   D on every nonzero Boolean row and zero on the zero row. Independently,
   evaluating at zero gives q0(0)=D, so q0 has an actual nonzero record.
5. `BooleanMobius.lean` defines a recursive Boolean-cube finite-difference
   transform. It proves linearity, exact coefficient extraction for every
   support mask, and a nonzero transformed coefficient at every nonempty
   mask for the nonzero-row indicator times D. Therefore each nonempty
   mask is the support of an actual transformed q_i record with nonzero
   coefficient. Cancellation and duplicate records do not bypass this
   implication.
6. `certificate_all_masks_covered` derives coverage of all `2^n` masks:
   charge the zero mask to a nonzero q0 record and the others to the
   transformed nonzero unit records. The complete mask list has no
   duplicates. The previously checked finite-list pigeonhole theorem
   gives the nonzero-record count bound.

`certificate_nonempty_mask_record` exposes the substantive witness step;
`sparse_certificate_bound` is the underlying rational Boolean-evaluated
certificate theorem. Neither assumes the desired cover property.

## Scope of the polynomial identity statement

`RationalCertificate` is a semantic polynomial identity on all rational
points, using actual sparse monomial evaluation. A coefficientwise formal
identity in Q[x_0,...,x_(n-1)] implies this evaluation identity by ordinary
polynomial interpretation. That implication/equivalence is mathematical
context here: this project does **not** define a coefficientwise formal
polynomial-ring equality datatype or prove its equivalence to equality
on all rational points. The theorem starts from the displayed, explicitly
defined rational evaluation identity and derives the entire sparse bound.
There is no informal rational denominator-clearing step; coefficients
throughout the proof are core Lean `Rat`.

The file proves the total `2^n` record bound. The stronger separate
`sum_i mon(q_i)>=2^n-1` inequality and sharpness by the prefix certificate
remain mathematical statements in `ALGEBRAIC_FOLLOWUP_REVIEW.md`; this
file does not claim them as additional formal theorem statements.

## Consequences and limits

The original clause list has O(n) literal occurrences, while every valid
certificate in this explicit sparse coefficient format needs at least
`2^n` nonzero records. Any ordinary encoding that explicitly writes each
record inherits at least that many record positions. Encoding bit costs,
parsers, verification algorithms, and running-time bounds are not
formalized here.

The format matters. Shared arithmetic circuits or factored coefficients
can encode a short prefix certificate and are outside this sparse-record
lower bound. The formulas themselves have an elementary unit-clause
refutation and are computationally easy. This establishes no general
proof-complexity lower bound, NP versus coNP separation, PIT impossibility,
or P versus NP result. No novelty claim is made.

## Verification and independent review

Compiled with installed Lean 4.35.0 and project `LEAN_PATH`:

```powershell
$env:LEAN_PATH = (Get-Location).Path
& C:\Users\email\.elan\bin\lean.exe frontier\SparseCertificateBound.lean
```

Exit code 0, no warnings. Printed axioms for the support-evaluation bridge,
derived coverage, Boolean bound, rational specialization, and final
rational/total bounds contain only `propext`, `Classical.choice`, and
`Quot.sound`. There are no placeholders, new axioms, `native_decide`, or
proof-time IO shortcuts.

An independent read-only audit of the main file checked the actual
exponent-token bridge, total rational evaluation hypothesis, filtered
record counts, and derived support coverage; it found no mathematical
flaw. It confirmed the formal-polynomial-ring and verifier-complexity
scope limits above.