# Two-gate functions paired with a primary-input NAND

This catalogue uses only primary inputs and binary NAND gates. Repeated fanins, unrestricted fanout, and any signal as an output are allowed. Constants and complements are not free. `C(f)` counts gates for one output; `J(f,g)` counts the shared gates producing both outputs. Here `C(f)=2` and `g=NAND(x_i,x_j)`, including i=j.

On five inputs the implementation enumerates every topologically ordered gate list of length zero, one, and two: 1, 25, and 900 lists respectively. It retains duplicate-function gates and unused gates, and examines every possible output selector. Thus it does not depend on a semantic-pruning argument. The initial signals are exactly the five variable truth tables.

## Complete classification

In a minimal two-gate circuit the output must be the second gate. Otherwise the first gate or a primary input already computes the output with at most one gate. The second gate cannot use only primary inputs for the same reason. Write the first gate as q=NAND(a,b).

* If both second-gate fanins are q, the output is a AND b. The inputs must differ, since a AND a is a primary input.
* If one second-gate fanin is q and the other is a primary input k, the output is NOT k OR (a AND b). When a,b,k are all distinct this is the three-variable family. If some labels coincide, Boolean absorption gives either the constant one function or an implication between two distinct variables.

This proves the four-form list is exhaustive. Each form has a two-gate construction, and none is a primary input or a NAND of primary inputs. The direct Boolean formulas are also compared with the exact set of functions first appearing at gate count two.

| Function family | Parameters on five inputs | Functions | J=2 pairs | J=3 pairs | Pair orbits |
|---|---|---:|---:|---:|---:|
| 1 | none | 1 | 5 | 10 | 2 |
| a AND b | unordered distinct a,b | 10 | 10 | 140 | 5 |
| NOT a OR b | ordered distinct a,b | 20 | 40 | 260 | 7 |
| NOT k OR (a AND b) | distinct k,a,b; a,b unordered | 30 | 30 | 420 | 8 |
| Total | | 61 | 85 | 830 | 22 |

The 15 possible g functions give 61*15=915 pairs. Permuting all five input labels gives 22 pair orbits: five with J=2 and seventeen with J=3. An independent BigInt JavaScript enumeration reproduced these counts and family breakdowns.

## Exact joint costs without SAT

Since C(f)=2, the joint cost is at least two. Appending the one gate for g to a minimum circuit for f gives a three-gate witness, so J is either two or three.

If a two-gate circuit computes both, f is its second output and g must be its first gate: g is neither a primary input nor f. Consequently J=2 exactly when a two-gate circuit for f can have g as its first gate. Complete gate-list enumeration tests this condition. The first-gate possibilities are:

| f | Possible first-gate g for J=2 |
|---|---|
| 1 | NOT x for any primary input x |
| a AND b, a != b | NAND(a,b) |
| NOT a OR b, a != b | NOT b or NAND(a,b) |
| NOT k OR (a AND b), three distinct inputs | NAND(a,b) |

For every other g the absence of a two-gate witness, together with the appended three-gate construction, gives J=3. These first-gate sets are checked against the independent structural classification in the tests.

## Why five inputs cover this subclass

Take a minimum two-gate circuit for f. The case analysis above shows it uses at most three distinct primary labels; g uses at most two. Retain the union of these labels, of size at most five. This argument uses labels from an actual circuit, so it also covers the constant-one function, whose circuit still needs a primary input.

Adding dummy input variables does not reduce NAND gate complexity when at least one retained input exists. Given a circuit whose target ignores the dummies, replace every occurrence of a dummy primary by one retained primary. This introduces no constant signal or gate, and the target is unchanged because it ignored the dummy coordinates for every assignment. Conversely, a circuit on the retained inputs works after adding ignored input coordinates. These two transformations prove equality of both single-output and shared-output minimum costs across the restriction/extension.

Here g depends on at least one variable, so the retained set is nonempty. Relabeling the retained coordinates and padding to five therefore preserves C(f), J(f,g), and every C(h(f,g)). This is a mathematical coverage argument for this restricted subclass. It is not a machine-checked Lean refinement theorem.

## Certificates and reproducibility

`results/low-cost-two-n5.json` contains all 22 canonical pair representatives, their orbit sizes, minimum single and joint gate lists, output selectors, formula parameters, and complete first-gate options. Canonical representatives are the lexicographically least pair of truth masks among all 120 input permutations. Bit a of a mask is the output on input xi=(a>>i)&1.

Each of the 915 internally constructed joint witnesses is checked by independent Boolean simulation. The tests independently simulate and relabel all representative witnesses, reconstructing exactly 915 distinct pairs with the stated orbit sizes. They also compare the two-input case with the existing independent complete state-space BFS, check the support histogram, dummy-input substitution, strict input types, refusal boundaries, and witness tampering.

```python
from continuation.low_cost_two import build_catalogue, verify_witness
result = build_catalogue(5)
assert result['status'] == 'EXACT_FINITE_ENUMERATION'
entry = result['catalogue'][0]
assert verify_witness(5, [entry['f'], entry['g']],
                      entry['joint_witness'], entry['joint_cost'])
```

`python -B -m continuation.low_cost_two` prints the deterministic report. `python -B -m unittest continuation.test_low_cost_two -v` runs nine focused offline tests. Source hashing normalizes CRLF and CR to LF; the saved report is compared with a fresh enumeration.

The API accepts exact integer input counts 1..5. Hard limits are 1,000 enumerated gate lists and 200,000 pair-permutation comparisons. A lower caller cap that interrupts completion returns `UNKNOWN` without a catalogue; malformed arguments return `MALFORMED`. The five-input run needs 926 lists and 109,800 pair-permutation comparisons. No SAT solver or API is used. No large five-input scalar-profile search has been run, and these results do not establish a general scalarization or solve P versus NP.
