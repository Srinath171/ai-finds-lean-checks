# Optimal NAND-circuit search with an arbitrary-output decision oracle

Status: independently AI-reviewed ordinary mathematical proof, not Lean-formalized or implemented here. No human acceptance or novelty claim is made. The oracle in this note has an unbounded, input-supplied number of outputs. It is not ordinary single-output MCSP and not the restricted two-output oracle studied elsewhere. P versus NP and scalarization remain unresolved.

## 1. Model and theorem

Fix n>=1 and N=2^n. Circuits are acyclic DAGs of two-input NAND gates with repeated fanins allowed. Primary inputs and output selectors are free; constants and negations are not free. Gate count is the number of NANDs, including any gates used to synthesize constants.

The decision oracle Joint accepts a list of total n-input truth tables F_1,...,F_r and a binary threshold s. It answers yes exactly when ONE shared NAND DAG of at most s gates has selected output wires computing every listed function on all inputs. Output selectors may name the same wire for duplicate functions. The output count r is part of the query and may grow polynomially with N.

**Theorem.** With this oracle, an optimal NAND circuit for an arbitrary supplied N-bit truth table f can be found by a uniform deterministic oracle algorithm with polynomial classical bit work and polynomial total query-writing length in N. The result uses no uniqueness or enumeration assumption about optimal circuits.

## 2. Prefix invariant

A selected prefix consists of k actual NAND gates, each using only original inputs or earlier prefix gates. Let W=(w_1,...,w_k) be their total truth functions. Require that all w_i are distinct and none is an original input projection. All truth functions are stored explicitly, so these checks are exact comparisons of N bits.

For a fixed budget s, the invariant is

    Joint(f,w_1,...,w_k) <= s.

This is one common-witness condition. Separate oracle answers for each pair (f,w_i) do not supply it.

## 3. Cost-preserving normalization of a common witness

Suppose a witness C of S<=s gates computes f and all W. For each w_i choose one designated output wire computing it. Because w_i is not a primary-input function, this wire is a gate. Because the w_i are distinct, these k chosen gates are distinct.

Construct a new circuit as follows:

1. Prepend the already selected legal k-gate prefix computing W.
2. Delete the k chosen gates from C.
3. Retain every other C-gate in its original topological order. Redirect each fanin or output selector that named a deleted gate to the corresponding prefixed w_i wire; renumber all retained wires.

The new count is k+(S-k)=S. Every new prefix wire is earlier than every retained C-gate. Any retained dependency on another retained gate keeps its original earlier order. Hence the circuit is well-formed and acyclic.

On every original assignment, a redirected wire has exactly the function of the deleted original gate. Induction through the retained original gate order therefore preserves all retained functions and output values. The f-output is redirected as well if it was one of the deleted gates. The prefixed wires directly supply all W outputs.

The selected W may have occurred in any order in C, including one incompatible with the selected prefix order, and may have used different implementations. That is harmless: the replacement prefix is an independently legal computation of the same TOTAL functions. No original gate implementing a w_i is recursively expanded, and all chosen gates are replaced simultaneously. Existing DAG sharing among retained gates is preserved. Newly unused predecessors may remain; pruning them can only decrease cost.

## 4. A feasible new gate exists

First take s=C(f), the exact optimal single-output cost. Suppose the invariant holds but f is not yet any original-input or selected-prefix function. Normalize a witness as above. There must be at least one retained gate, since otherwise f would already be available.

The first retained gate has both fanins among the original inputs and W. Call its function h. If h equals any currently available function, redirect its uses to that available wire and delete the gate. This gives a circuit for f with fewer than s gates: normalization had at most s gates and the deletion removes one. This contradicts s=C(f). Thus h is a new function.

The normalized witness contains the original selected prefix followed by this gate and still supplies f and W. It therefore witnesses

    Joint(f,W,h) <= s.

Consequently among all NAND pairs of available wires, at least one semantically new candidate h passes the joint query. This is an existence proof for a decision-query search step, not an assumption that the oracle returns a circuit.

A stronger budget-only variant also follows: among normalized witnesses respecting the fixed prefix and a feasible upper budget, choose one with the fewest retained gates. A first retained gate duplicating an available function could be removed, contradicting that minimum. Hence a new feasible candidate exists even without a globally optimal budget. The optimal-budget version above is sufficient for the theorem.

## 5. Algorithm and termination

Start with the primary input tables and empty W. If f equals a primary input, return that wire at cost zero. Otherwise, obtain the optimum s by binary search with single-output queries Joint(f)<=s. These are allowed special cases of the arbitrary-output oracle.

At each prefix stage, compute every ordered NAND pair of the n+k available wire tables, including repeated fanins. Skip any candidate table equal to an available table. For each remaining h ask Joint(f,W,h)<=s. Append the first candidate receiving yes, recording its actual two fanin indices and its table. Stop when f is available and select its wire as output. Section 4 guarantees that the candidate search cannot fail while the invariant holds and f is unavailable. Every accepted candidate preserves the invariant by its oracle answer.

Distinct noninput functions require distinct gates in any common witness. Therefore k<=s. If k=s and f is still unavailable, the queried output functions f,w_1,...,w_k would be k+1 distinct noninput functions and need at least k+1 gates, contradicting the invariant. Thus the algorithm stops in at most s append steps. Its recorded prefix is a valid circuit for f with at most s gates, hence exactly optimal when s=C(f).

The algorithm never needs to recognize a particular optimal witness, to assume that its intermediate functions occur in the selected order, or to count near-optimal circuit copies.

## 6. Truth-table and bit-cost bounds

Use the explicit constructive universal bound

    B(n)=3+(3n+7)*2^n=O(N log N).

Binary search needs O(log(B(n)+1)) oracle answers and thresholds with O(log(B(n)+1)) bits. A supplied larger yes-budget may be clipped to B(n) for the single-target search. The search stage has at most s iterations and at most (n+s)^2 pair queries per iteration, so at most s(n+s)^2 queries in total.

Each query keeps arity n and explicitly supplies at most k+2<=s+2 N-bit output tables, plus its threshold and framing. Its writing length is O((s+2)N+log(s+2)) up to ordinary delimiters. Total query bits are therefore at most

    O(s(n+s)^2 * ((s+2)N+log(s+2))).

Candidate construction uses N NAND bit operations; duplicate checks compare against at most n+s N-bit tables. All indexing, arithmetic and gate-description overhead has polynomial bit cost. Since s<=B(n)=O(N log N), both these computations and all explicitly charged query writing are polynomial in N. Recording the output circuit takes O(s log(n+s+1)) bits. No table on n+k input variables is created.

The result is about oracle complexity, not an ordinary polynomial-time minimization algorithm: no polynomial-time implementation of Joint is supplied or assumed to have been proved. A no-input model n=0 is excluded because NAND gates cannot synthesize a signal without an initial wire. For n>=1, constant targets are generated normally with paid gates.

## 7. Exact remaining scalarization gap

The oracle used during the k-th stage jointly constrains f and EVERY chosen prefix function plus the next candidate. Its output count grows with k. A restricted oracle deciding only Joint(f,g), where g is one known NAND of two original inputs, cannot make these queries. Even a general two-output oracle does not automatically force compatibility with all previous choices: `for each i there exists a witness` is not `there exists one witness for all i`.

Likewise, encoding all these output tables into one scalar truth table by a selector requires a separate exact size-preserving or threshold-correct reduction; multiplexing alone proves no such property. The prefix normalization succeeds precisely because every named feature is a TOTAL function already required by the common oracle witness. It does not choose off-graph values for a partial extension and does not close the ordinary-MCSP search-to-decision problem.

This lemma isolates a valid stronger-oracle search procedure. It does not settle the main exact two-output-to-single-output bridge, establish general MCSP hardness, or solve P versus NP.
