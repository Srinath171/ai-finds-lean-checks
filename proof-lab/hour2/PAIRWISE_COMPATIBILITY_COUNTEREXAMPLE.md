# Pairwise optimal compatibility does not give a common witness

Take the actual two-input shared NAND-DAG model, with original inputs x,y, no free constants, arbitrary sharing and freely selected output signals. Let

```text
f = constant1,  s=C(f)=2,
h1 = NOT x = NAND(x,x),
h2 = NOT y = NAND(y,y).
```

The first candidate gate h1 uses original inputs. The second h2 is a legal next gate after h1: it uses the still-available input y twice and computes a new function, distinct from x,y,h1. Thus it satisfies the requested syntactic prefix restriction, although it does not need to use h1 as a fanin.

Each candidate is individually compatible with an optimal f circuit. Actual witnesses, with original inputs at indices0,1, are

```text
f,h1: [(0,0),(0,2)], outputs[3,2]       # cost2
f,h2: [(1,1),(1,2)], outputs[3,2]       # cost2.
```

A constant-one output is neither original input. One NAND of two original inputs can only produce NOT x, NAND(x,y), or NOT y; none is constant one. Hence C(f)>=2, and the displayed circuits show C(f)=2. Consequently both individual joint costs equal s=2.

There is no common witness at budget2. The three target truth functions constant1, NOT x and NOT y are pairwise distinct and none is an original input. Every target must therefore select a gate-output signal, and distinct functions require distinct signals. Two gates cannot supply three distinct gate outputs. Three gates suffice:

```text
[(0,0),(1,1),(0,2)], outputs[4,2,3].
```

Thus `J(f,h1)=J(f,h2)=2`, but `J(f,h1,h2)=3`. After committing both prefix gates, f is still not an available signal; one additional NAND is needed. A greedy test using only the separate two-output conditions can therefore accept two individually compatible choices with no common optimum. The missing quantifier is one shared witness satisfying ALL accumulated choices, not a separate existential witness for each pair.

[The concrete report](results/pairwise-compatibility-counterexample.json) records every reachable two-input function-set state through three gates, transition counts, a canonical LF hash and actual witnesses. State counts by exact gate count are [1, 3, 10, 27]. The complete bounded enumeration finds no budget-at-most-two state containing all three target masks15,5,3. All supplied witnesses were checked on every assignment by a separate Boolean evaluator; both two-output witnesses also pass the existing `joint_nand.verify_witness` checker. No solver or model/API call was used.

The function-set enumeration removes only duplicate-function gates: any later use of such a gate can be redirected to an earlier identical signal without changing semantics or increasing cost. The report is finite exhaustive computational corroboration, not a Lean-checked enumeration. The elementary three-distinct-noninput-signals lower bound above is independent of that enumeration. This counterexample refutes pairwise-to-common compatibility only; it supplies no general search-to-decision reduction or P versus NP conclusion.
