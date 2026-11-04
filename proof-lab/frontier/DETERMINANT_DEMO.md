# Exact determinant-three derivative example

This is a finite exact check supporting the illustration in [the general determinant argument](DETERMINANT_SPARSITY.md). It is not a replacement for that all-size proof, a Lean certificate, or a P versus NP result. No novelty or human review is claimed.

Use row-major matrix coordinates and the all-ones point. Write f(T)=det(exp(T_ij)), with exponential applied entrywise. The six columns below follow lexicographic permutation order, with their determinant signs included.

| Derivative | 012 | 021 | 102 | 120 | 201 | 210 |
|---|---:|---:|---:|---:|---:|---:|
| f | 1 | -1 | -1 | 1 | 1 | -1 |
| D22f | 1 | 0 | 0 | 0 | 0 | -1 |
| D33f | 1 | 0 | -1 | 0 | 0 | 0 |
| D23f | 0 | -1 | 0 | 1 | 0 | 0 |
| D32f | 0 | -1 | 0 | 0 | 1 | 0 |
| D22D33f | 1 | 0 | 0 | 0 | 0 | 0 |

The exact determinant is **1**. Independent rational elimination gives rank **6**. These are the coefficient vectors of six derivatives in the span of the six actual signed monomial exponentials.

All constant and linear Taylor coefficients of f vanish. Put

```text
U = T22-T21-T12+T11
V = T23-T21-T13+T11
W = T32-T31-T12+T11
Z = T33-T31-T13+T11.
```

The complete initial quadratic is UZ-VW. All 45 degree-two coefficients were independently compared with the exponential-moment formula, giving 18 nonzero terms. The six displayed derivatives have lowest parts UZ-VW, Z, U, -W, -V, and 1, respectively. The four linear forms are independent, as seen from their distinct T22,T23,T32,T33 coefficients. Thus their lowest parts are independent across homogeneous degrees.

[The exact data](results/determinant3-derivative-demo.json) records all permutations, exponents, signs, derivative selectors, the full matrix, the leading quadratic and a digest. The `report_sha256` field hashes compact sorted-key ASCII JSON after removing that field, without a final newline; it is not the pretty-printed file byte hash. The determinant was computed by all 720 Leibniz terms, independently of the elimination rank. The general rational-GL and affine statements remain independently AI-reviewed mathematical arguments outside Lean.

From proof-lab this short standard-library check reconstructs the coefficient matrix and its determinant from the specified exponent data:

```python
from pathlib import Path
from itertools import permutations
from math import prod
import json
r = json.loads(Path("frontier/results/determinant3-derivative-demo.json").read_text())
def sign(p):
    return (-1)**sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))
ps = list(permutations(range(3)))
assert [list(p) for p in ps] == r["permutations"]
es = []
for p in ps:
    e = [0]*9
    for i,j in enumerate(p): e[3*i+j] = 1
    es.append(e)
ws = [sign(p) for p in ps]
assert es == r["monomial_exponents"] and ws == r["monomial_weights"]
a = [[w*prod(e[j] for j in s) for e,w in zip(es,ws)]
     for s in r["selectors"]]
assert a == r["coefficient_matrix"]
det = sum(sign(p)*prod(a[i][p[i]] for i in range(6))
          for p in permutations(range(6)))
assert det == r["matrix_determinant"] == 1
print("Six independent determinant derivative vectors verified")
```
