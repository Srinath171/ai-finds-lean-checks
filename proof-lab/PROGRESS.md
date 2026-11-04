# Research checkpoint

The original P versus NP target remains unresolved. The latest offline replay passes **353 Python tests in 21.453 seconds**, with no skips. **29 Lean research modules** have compiled across the original 23-source replay and independent postchecks of 2+1+1+1+1 modules; no single combined 29-module run is claimed. [Verification records](results/verification.json) contain exact source hashes and log provenance. Verification made no paid API calls.

## Complete restricted mathematical arguments

For F_m = product_i x_i*y_i*(x_i+y_i), the [normal-crossing argument](frontier/NORMAL_CROSSING_SPARSITY.md) establishes minimum global monomial sparsity 2^m under arbitrary invertible rational linear changes, for every m. A separate highest-degree-component argument extends this minimum to invertible affine changes. The earlier four-block checkpoint is superseded.

The extra structural information is an exact crossing with m independent initial linear factors at a point whose coordinates are all nonzero. After logarithmic substitution, its 2^m dual-direction derivatives have independent lowest homogeneous parts, while all lie in a space spanned by the actual sparse monomials' exponentials. A determinant-permutation matching supplies the required crossing point for every invertible presentation. The same reasoning gives h_r(E) >= sum_(k<=min(r,m)) binomial(m,k), including the previously missing h_2(E)>=16 for F_5.

The complete argument is **independently AI-reviewed, not fully Lean-formalized or human/peer-reviewed**. Muse Wonder MAX and regular Claude both returned visible critiques finding no substantive gap. Their [recorded outputs](frontier/results/normal-crossing-audit.json) are critiques, not proof certificates. No novelty claim is made.

The general derivative-space principle also yields an [AI-reviewed determinant application](frontier/DETERMINANT_SPARSITY.md): every rational invertible linear or affine presentation of det_n needs at least binomial(2n-2,n-1) monomials. This gives exact minima 2 and 6 for n=2,3; n=4 remains bounded between 20 and 24. This extension is also unformalized and is not implemented by the factor-block Python constructor.

These are expanded-representation bounds. The explicit product family already has a small arithmetic formula, and determinant has efficient circuits. Neither result separates complexity classes, provides general PIT, or proves a general circuit/proof-system lower bound.

## Checked components and runnable code

[TriangularDimension.lean](frontier/TriangularDimension.lean) constructs an actual rational inverse for a lower-triangular matrix with nonzero diagonal, then proves that an actual rectangular product AB of that form requires N<=W. Independent compilation printed only standard axioms. This conditional matrix theorem does not formalize the whole orbit argument.

The [geometry constructor/checker](frontier/NORMAL_CROSSING_CHECKER.md) verifies actual invertibility, a rational torus point, exactly the selected m zero factors, nonzero remaining-factor product C, rank and scaled normal duals. It is bounded to m<=6 and may enumerate 3^m choices; it is not a polynomial-time general solver.

The [moment pipeline](frontier/NORMAL_CROSSING_MOMENTS.md) additionally expands the actual polynomial for m<=3, computes every entry of actual A, B and AB, and checks the triangular zeros and nonzero diagonal. A dense m=3 fixture has 2002 monomials and uses444,301 aggregate operations. Refusals carry no width verdict. Independent audits and regressions cover altered certificates, alternative duals, exact cap-73/cap-143 refusals and the scope of the bit-size metric. The Python programs are not Lean-refined implementations.

From proof-lab, this offline example prints VERIFIED_MOMENTS 8 8:

```powershell
.\.venv\Scripts\python.exe -B -c "from frontier.normal_crossing_moments import analyze_moments; a=[[int(i==j) for j in range(6)] for i in range(6)]; r=analyze_moments(a,m=3); print(r['status'], r['term_count'], r['width_lower_bound'])"
```

Earlier verified results remain recorded: [coordinate-domain soundness](frontier/COORDINATE_CHANGE.md), [optimal-support obstruction](frontier/OPTIMAL_SUPPORT.md), [rational sparse-certificate lower bound](frontier/SPARSE_CERTIFICATE_BOUND.md), and [subset-zeta kernel](frontier/SUBSET_ZETA.md). The [30-point bare-moment counterexample](frontier/SPARSITY_MOMENT_OBSTRUCTION.md) remains valid; the new proof uses the independent-product initial form that its premises omit.

## Spending, access and remaining blockers

The new complete-proof Wonder MAX audit finished with visible output at recorded cost **$0.218024**. The earlier open-ended orbit probe exhausted its output allowance without a visible answer and recorded $1.314964; it was not repeated. Local commitments INCLUDING holds are **Meta $33.442536/$125; Claude API $6.82518/$40**. Settled research API records total $6.958936 and $5.82518; four old uncertain Meta reservations remain held. These are cooperating-client records, not account-wide invoices. The Meta billing page did not load on the last authorized check. See [spending details](results/spending-checkpoint.json).

No paid job or automatic paid loop is active. No setup or approval input is pending. The original deadline remains **2026-11-04 19:42:17 UTC**. Deliberate access and changes stay within this project and the specifically authorized tools/accounts; unrelated root application changes are outside the research commit.

For the original P versus NP objective, no general short-certificate guarantee, eligible-class worst-case SAT saving, or unrestricted Partial-MCSP-to-total-MCSP reduction has been established. Completing formal verification of the new restricted arguments is a separate engineering task and would not itself resolve that complexity-class gap.

## Final verification map

[GradedDimension.lean](frontier/GradedDimension.lean) adds an actual grade-wise inverse and dimension bound, removing sorting from the conditional matrix step. Its independent replay and source audit passed with standard axioms only. The full mathematical application is still outside Lean; [the dependency and trust map](frontier/FORMALIZATION_GAPS.md) states exactly which links remain.

[The determinant-three example](frontier/DETERMINANT_DEMO.md) records six derivative vectors with exact matrix determinant 1, independently checked by Leibniz expansion and rational elimination. Its complete initial quadratic was also verified. This is a finite illustration of the separate general argument.
