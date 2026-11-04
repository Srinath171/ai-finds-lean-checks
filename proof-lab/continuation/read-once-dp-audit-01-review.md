# Read-once strict-NAND DP: independent Meta audit

The single requested Muse Wonder MAX job completed normally with a finished 824-word answer and verdict **VALID**. The guard reported terminal/completed, no incomplete output or error, and settled recorded cost **$0.447812**. The fixed job limit was 900 seconds. Only the public algorithm prompt was sent; no project source, file attachment, secret or account data was included. No second model call was made.

The raw [visible answer](read-once-dp-audit-01-response.txt), [exact prompt](read-once-dp-audit-01-prompt.txt) and [sanitized result metadata](read-once-dp-audit-01-result.json) are retained separately. This is an independent AI mathematical audit, not human peer review, implementation testing or a Lean proof.

## Local review of the argument

I found no missing mathematical step under the exact promise: f is nonconstant on d>=1 original labelled variables and every one is essential; the only paid gate is binary NAND, with no free constants or complemented inputs.

The equality case in the essential-input bound is the main structural point. After pruning the output cone, all d essential inputs remain. Connectivity gives at least d+m'-1 distinct edges, while m' binary gates have at most 2m' fanin edges. At m=d-1 all inequalities are equalities, so no gate is unused, no fanin pair repeats the same edge, and the connected graph is a tree. Orienting it toward the selected output makes every non-output signal have one successor. Thus the actual DAG really is read-once; the argument does not assume this in advance. The d=1,zero-gate case is the positive primary input.

Signed-cofactor state generation is complete. Ancestor siblings in a read-once tree use disjoint variables and each can attain 1, so fixing them to 1 exposes any subtree up to Boolean complementation. Exact support reduction preserves the original variable labels. More generally, any candidate child formed from a signed reduced cofactor is still a signed cofactor of f: extend the original restriction by the chosen row/column assignment and fix any removed inessential variables arbitrarily. No relabelled or free-complement state is silently substituted.

The arbitrary-zero normalization is valid over Boolean values: if q=NAND(g,h) and q(u0,v0)=0, then g(u0)=h(v0)=1. The selected row and column therefore recover the actual factors. Conversely, the full-entry test explicitly establishes q=NAND(g,h). If a recovered child ignored a variable assigned to its part, q would ignore that variable too, contradicting its exact essential support. Accepted children consequently have the required full disjoint supports, and the literal reconstructed gate count is (|U|-1)+(|V|-1)+1=|K|-1.

The strict-basis safeguards are necessary and present: positive singleton inputs accept with zero gates, negative singleton inputs do not, and making a complemented TABLE never creates a free NOT gate. NAND(x,y) accepts. For the three-input NAND, its rank-one complement factorization exposes an AND child; that child fails the strict-basis DP, so the two-gate target rejects as required.

## Complexity and implementation conditions

The bounds are achievable with direct restriction-table generation. Summing table lengths over ternary restrictions gives poly(d)*4^d; a state's partition count times its table scan is at most poly(d)*4^k for essential support size k, and summing over cofactor states gives poly(d)*6^d. Stored state tables, canonical keys and split pointers fit poly(d)*4^d space. These are polynomial bounds in the FULL truth-table input size 2^d, not subexponential bounds in d.

To retain a deterministic worst-case bound, canonicalize exact labelled tables with a suitable deterministic dictionary/trie (or otherwise account for collision handling). Generate each restriction directly from its star coordinates and process candidate partitions without retaining all temporary tables. These are implementation requirements for the stated bounds, not a mathematical repair to the recurrence.

No implementation of the proposed DP was exported, run or verified by this audit. The conclusion concerns recognition/reconstruction at the special lower-bound equality C(f)=d-1; it does not establish a general circuit-minimization or P versus NP result.
