# Exact one-gate graph rows and holes

`GraphHoles.lean` imports only `frontier.FirstGateExtension` (which imports
`frontier.MCSPScope`) and uses the existing complete assignment enumeration.
For a Boolean prefix `a` of length `n`, its two appended rows are

```
graphInput a i j   = a ++ [NAND(a_i,a_j)]
missingInput a i j = a ++ [NOT NAND(a_i,a_j)]
```

`graphRows n i j` and `missingRows n i j` map these functions over
`MCSPScope.allAssignments n`.

The checked API in namespace `GraphHoles` includes:

- `length_graphRows`, `length_missingRows`: each length is exactly `2^n`.
- `nodup_graphRows`, `nodup_missingRows`: those lengths count distinct rows.
- `graphRows_disjoint_missingRows`: no row belongs to both enumerations.
- `graph_or_missing_of_length`, `graph_and_missing_cover`: together they
  cover precisely every Boolean list of length `n+1`.
- `missingRows_enumerates_holes`: membership in `missingRows` is equivalent
  to membership in `allAssignments (n+1)` and nonmembership in `graphRows`.
- `nodup_graph_missing_partition`, `length_graph_missing_partition`: their
  concatenation is duplicate-free and has length `2^(n+1)`.
- `mem_graphRows_iff_last`: for `i<n` and `j<n`, graph membership is exactly
  the valid-width condition and the NAND equation at the last coordinate.

The enumeration/count statements do not require index bounds: appending
any Boolean function always partitions the rows in this way. When applying
them to an actual first NAND gate, use `n>=1`, `i<n`, and `j<n` from its
well-formedness conditions. No projection or optimal-support hypothesis is
hidden in these counts. The file does not prove the separate claim that
an optimal extension must use all coordinates, nor any complexity-class
separation.

Compiled with the project-pinned Lean **4.35.0**, exit code zero and no
warnings. All printed theorem axioms are subsets of
`propext`, `Classical.choice`, and `Quot.sound`. There are no placeholders,
new axioms, `native_decide`, paid calls, or network operations.
