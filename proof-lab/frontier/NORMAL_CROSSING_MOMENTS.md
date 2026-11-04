# Exact finite normal-crossing moment matrices

`normal_crossing_moments.analyze_moments(matrix, m=1..3)` computes one bounded supplied-matrix instance. It first calls the full sparse expansion checker for `F_m(Az)` and then independently verifies an actual normal-crossing point, selected factors, nonzero remaining-factor product C and normal dual Y. The dual satisfies `(selected_rows * diag(p)) Y = I`. Geometry alone never produces a verified moment result.

For every actual nonzero exponent/coefficient record alpha, the code computes

```text
v_alpha = c_alpha * product_j p_j^alpha_j
q_(i,alpha) = sum_j alpha_j * Y_(j,i)
A_(S,alpha) = v_alpha * product_(i in S) q_(i,alpha)
B_(alpha,T) = product_(i not in T) q_(i,alpha).
```

All rational values are exact `Fraction` objects. Subsets are ordered by `(popcount, mask)`. The code multiplies these ACTUAL rectangular matrices and checks every upper entry is zero and every diagonal entry equals the independently verified nonzero C. It does not fill in the desired triangular pattern or accept supplied sparse-coefficient or moment claims. The result includes the actual full sparse expansion, weights, features, A, B, and AB.

`VERIFIED_MOMENTS` means these bounded rational calculations passed. It is not a Lean-checked certificate, a formal refinement of the Python code, a universal orbit theorem or a P versus NP result. The separate generic triangular-product dimension theorem does not itself formalize the geometric, expansion, derivative or orbit application. Singular input, malformed input, rejected geometry, resource refusal and inconsistent actual moments remain distinct outcomes with no width verdict.

## Limits and reproducible evidence

The fixed maximum is m=3, input numerator/denominator bits at most 32, intermediate rational bits at most 8192, aggregate arithmetic operations at most 2,000,000 and sparse terms at most 4096. Limits can only be lowered. Expansion and geometry operation counts are charged to the same aggregate allowance before the moment calculation; dependency-specific limits remain in force. The public `moment_max_fraction_bits` metric covers values observed by the moment meter (including copied input/geometry values) and its own arithmetic. It does not claim to report unexposed peak intermediates inside expansion or geometry dependencies. Their own bit caps remain independently enforced. `operations` counts completed arithmetic across stages; a refused next moment operation is checked before incrementing that counter.

No network, environment, secrets, filesystem access, model call or code evaluation is used by this module.

An optional `geometry_certificate` is reverified from the actual matrix and must include a valid dual. Altered points, duals or products are rejected. No API accepts a submitted A/B/AB certificate as already verified.

[The demo](results/normal-crossing-moments-demo.json) records identity fixtures m=1,2,3, a nonsymmetric rational fixture and a dense m=3 fixture with all 2002 degree-nine monomials. Hashes use compact sorted-key ASCII JSON with normalized rational pairs and exactly one final LF. For the m=1 identity matrix, the exact normalized input is

```text
[[[1,1],[0,1]],[[0,1],[1,1]]]

```

and its SHA256 is `7bee1214bf24469d26cfaae5585d55dc1f1be590df5695bdd72b51886ae6c61a`.

Eight focused tests passed, including a cap-73 geometry refusal-accounting regression and a tight cap-143 moment-stage regression. They compare every AB entry for identity m=1..3 and the nonsymmetric rational fixture against an independently expanded original factor-product jet at `p*exp(Yu)`, rather than reproducing the global-coefficient moment code. The dense fixture also checks the independent initial Taylor jet. Negative tests cover corrupted geometry, missing duals, singular/malformed inputs, caps and exact LF hashing.
