# Arbitrary exponents and Boolean support collapse

`SparseMonomial.lean` uses sparse records `(exponentVector, rationalCoefficient)`. Exponents are unrestricted natural numbers, not assumed to be zero or one. Records may repeat and coefficients may be zero. Every exponent vector is evaluated against a same-width variable list; mismatched widths return zero.

`boolPow` is repeated Boolean multiplication. `exponentEval` evaluates these arbitrary exponent vectors, while `support` replaces each positive exponent by `true` and zero by `false`. The squarefree evaluator is `maskEval`. The kernel-checked `collapse_eval` proves that their Boolean values agree, for every exponent vector and assignment, including mismatched widths.

`collapseTokens` maps each record to its support mask with the same coefficient. `collapse_length` proves that the record count is unchanged. It does not claim that records are already distinct or that coefficients have been combined; retaining duplicates and zero coefficients avoids hidden normalization assumptions. `collapse_value` proves exact equality of rational sparse-record values on Boolean inputs.

The bridge also includes actual rational monomial evaluation, not just Boolean syntax:

```text
ratMonomialEval (e::es) (x::xs) = x^e * ratMonomialEval es xs
boolEmbed a = a.map (fun b => if b then 1 else 0)
ratMonomialEval es (boolEmbed a) = ratValue (exponentEval es a)
ratPolyValue p (boolEmbed a) = expPolyValue p a
```

The powers in `ratMonomialEval` are Lean's ordinary natural-number powers over `Rat`. `ratValue_boolPow` proves the embedding law by induction using `Rat.pow_succ`. Thus evaluation at Boolean points of sparse polynomials with arbitrary powers can feed the squarefree-mask argument without assuming the original certificate is multilinear.

This file does not define a full multivariate polynomial ring, prove uniqueness of polynomial coefficients, or formalize binary encoding/bit complexity. It supplies a faithful evaluation and record-count bridge for the separate certificate argument. A certificate identity at all rational inputs implies its Boolean specialization through these lemmas; that specialization alone is not a P versus NP result.

Compiled cleanly with Lean 4.35.0. Printed dependencies use only `propext`, `Classical.choice` and `Quot.sound`; no new axioms, placeholders, `native_decide` or proof-time IO are used.
