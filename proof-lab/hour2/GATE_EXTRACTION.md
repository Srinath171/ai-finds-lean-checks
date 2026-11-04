# Arbitrary-gate extraction and exact shared-output cost

`GateExtraction.lean` proves circuit surgery for an arbitrary designated NAND gate in the existing independently well-formed shared-DAG model. It then proves the exact finite shared-output cost identity for `g(x)=NAND(x_i,x_j)`, where i and j are valid original-input indices (including i=j).

## Actual gate surgery

Write the original gate list as `pre ++ [designatedGate] ++ post` and let `t=pre.length`. The prefix and suffix are arbitrary; the designated gate need not be the first gate or syntactically use original inputs. Its actual computed value is named `gateValue`.

The extracted circuit has n+1 primary inputs, with the new free input z at index n. It deletes the designated gate and uses this exact old-wire map:

```text
original input w<n:                 w -> w
old gate n+k with k<t:            n+k -> n+1+k
old designated gate n+t:          n+t -> n
old gate n+k with k>t:            n+k -> n+k.
```

`extractionMap_cases` proves the piecewise map. The prefix is rewired using the general input-substitution theorem; at the boundary a coordinate permutation moves the deleted gate's value into the new free-input position. Every later use and the output selector are remapped. The construction preserves sharing, repeated fanins, unused gates and outputs selecting any original or computed signal, including the deleted gate itself.

`extraction_wellFormed` proves independent fanin and output-selector well-formedness. `extraction_length_eq_sub_one` proves the new gate count is exactly the old count minus one. `extraction_eval` proves equality with the original output on every valid original assignment when z receives the designated gate's actual original value. `extraction_computes_graph` replaces that actual value by any separately proved semantic function g. It does not assert that an arbitrary designated gate computes a desired g.

## Exact joint versus residual budgets

`JointBudget n f g S` means one legal shared n-input gate list with two legal output selectors computes f and g and uses at most S paid NAND gates.

`ResidualBudget n f i j e` means a legal (n+1)-input circuit uses at most e gates and agrees with f on EVERY row of the graph `z=NAND(x_i,x_j)`. Off-graph values remain unrestricted.

For valid i,j the theorem is

```text
joint_budget_iff_residual:
  JointBudget n f (inputNand i j) (e+1)
    iff ResidualBudget n f i j e.
```

The forward direction does not assume that the joint circuit starts with the g gate. On the all-ones input every original input is true while g is false, so the g output must designate an actual gate. `gate_signal_decomposition` locates that gate at its arbitrary position. Extracting that gate yields a residual circuit with one fewer paid gate and the correct graph agreement.

The reverse direction prepends one paid original-input NAND to a residual circuit. The new gate occupies exactly the old free-input index n, so no hidden additional computation is required. The two outputs select f's former output and that newly paid g gate.

## Attained minimum costs

`LeastJoint` and `LeastResidual` specify actual attained least gate budgets. `joint_residual_minimum_identity` proves that ANY such minima satisfy `J=e+1`. `exists_joint_residual_minima` additionally proves both minima exist for EVERY Boolean target f at the fixed valid width and indices: a universal finite circuit for f plus an appended paid NAND provides a joint witness; the exact budget equivalence gives a residual witness; the least-natural-witness principle supplies attained minima.

Thus the final cost identity is not conditional on an unproved efficient search procedure, an assumed first-gate property or missing existence of minima. The result concerns the precisely defined shared-output and graph-extension models. It does not equate either of them with a standard single-output total truth-table MCSP query, construct an efficient oracle reduction, prove a complexity-class separation or solve P versus NP. No novelty or external peer-review claim is made.

Compiled cleanly with the project's pinned Lean 4.35.0. Printed dependencies of the extraction semantics, exact budget equivalence and attained-minimum identity contain only `propext`, `Classical.choice` and `Quot.sound` (the surgery core needs only `propext` and `Quot.sound`). No new axioms, placeholders, `native_decide`, numerical solver or proof-time IO were used.
