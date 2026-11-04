# Six concrete four-gate support cases

`SixCaseSupport.lean` proves an actual four-gate upper bound and excludes every circuit with at most three paid NAND gates for each of the following six Boolean functions. All predicates use the existing independent shared-DAG well-formedness and `MCSPScope.Computes` semantics.

| Case | Valid input order | Function |
|---|---|---|
| H1 | a,b,z,t | NOT(a AND b) OR (z AND t) |
| H2 | a,b,z,t | (a AND NOT b) OR (z AND t) |
| H3 | a,b,c,z | (c AND NOT(a AND b)) OR (a AND z) |
| H4 | a,b,c,z | c AND (NOT(a AND b) OR z) |
| H5 | a,b,c,z | (c AND NOT(a AND b)) OR z |
| H6 | a,b,c,z,t | (c AND NOT(a AND b)) OR (z AND t) |

Each upper bound is a concrete legal four-gate list with a legal output selector. Its full Boolean semantics is verified on all valid four- or five-bit input lists, not inferred from a cost formula.

## Four-input lower bounds

For H1 through H5, the module performs one closed `decide` proof checked by Lean's kernel. The enumerated gate lists include every independently well-formed four-input list with zero, one, two or three gates. Ordered predecessor pairs are retained, so no fanin-commutativity or DAG-normalization completeness assumption is needed. Repeated fanins, sharing, unused gates and outputs selecting inputs or earlier gates are all covered.

The exact enumeration sizes are

```text
0 gates:1
1 gate:4^2=16
2 gates:4^2*5^2=400
3 gates:4^2*5^2*6^2=14,400
total:14,817 gate lists.
```

For each list, the check computes its final list of all available truth-table signal masks and verifies that none equals one of the five target masks. This avoids repeating the whole gate evaluation for every output-selector choice. The five masks are63351,61986,64112,61552,65392 in the table's respective input orders. Each target-mask equation is separately proved by kernel evaluation over its16 input rows.

`gateSeqsN_complete` supplies the actual gate-list coverage. `selN_eq_zero_or_mem` handles every output selector; the default-zero case cannot equal a target. The generic `computes_mask_eq` theorem uses the existing independent Boolean/mask semantics to connect a hypothetical `MCSPScope.Computes` witness to its target mask. Thus the excluded masks are connected to the actual legal circuit predicates, not merely an external truth-table calculation.

The computational proof uses `decide`, not `native_decide`. Compiler invocations were bounded by a180-second process watchdog. The final source compiled successfully without warnings or placeholders.

## Five-input lower bound

H6 uses a separate structural proof. Explicit pairs of valid assignments show that each of its five original inputs is semantically essential. The existing general shared-DAG dependency theorem says a circuit with at most s gates has at most s+1 essential inputs. At s=3 this permits only four, contradicting the five witnesses. This proof does not assume the circuit is a formula or a read-once tree.

The source exposes `H1_exact_four_boundary` through `H6_exact_four_boundary`, each giving `HasCircuit ... 4` together with `NOT HasCircuit ... 3`. All six exact concrete boundaries therefore follow in the stated NAND model.

## Scope

This file proves the six concrete cases. It does not formalize the classification of arbitrary cost-two functions into these normal forms, arbitrary input permutations/unused-input elimination, a global truncated-profile decision rule, or a general reduction. Those applications need their own explicit transport/classification arguments, even though the project already provides a general rewiring theorem. No complexity-class separation, P versus NP solution or novelty claim is made.

Pinned toolchain: Lean4.35.0. Printed dependencies contain only `propext`, `Classical.choice` and `Quot.sound`; the closed finite-coverage theorem itself uses only `propext` and `Quot.sound`. No new axioms, `sorry`, `native_decide`, numerical solver or proof-time IO were used.
