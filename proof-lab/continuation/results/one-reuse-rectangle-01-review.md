# Independent review: one-reuse-rectangle-01

Outcome: accepted as a local structural lemma, not a complete reconstruction theorem. The single guarded job finished successfully, with settled recorded cost USD 0.208484. It used 746 input tokens, 10275 output tokens including 8812 reasoning tokens, and 11021 total tokens. The guard reports seven HTTP requests including submission/polling; this is one model job. Its state is continuation/jobs/one-reuse-rectangle-01/state.json.

The CLI form originally supplied with --max-job-seconds900 was rejected by argparse before submission. The one submitted job used --max-job-seconds 900. No provider retry or second model job was launched.

Independent mathematical checks:

1. Every positive-leaf strict read-once NAND subtree is surjective, by induction and independent assignment of its disjoint child supports.
2. For A(z,X) with X nonempty, write the root as NAND(S,T), with z in S. The subtree T is surjective. Setting T=0 forces A_b=1, so no fixed-z cofactor is identically zero. If S is the leaf z, exactly b=0 gives constant 1. If S is internal, induction gives an assignment with S_b=1; combine with T=1 to obtain A_b=0, hence the cofactor is nonconstant. This proves the claimed if-and-only-if, including necessity.
3. For F=NAND(A(z,X),B(z,Y)) and disjoint nonempty X,Y, each fixed-z zero set is the Cartesian product of the two nonempty 1-supports. The projections therefore recover both supports uniquely. The entire zero slice may be a full rectangle; that edge case remains valid. Cofactors may lose essential variables without invalidating the proof.
4. The answer's projection scan and factorization verification use O(N) table operations for N=2^(1+|X|+|Y|), with O(2^|X|+2^|Y|) auxiliary space. These are indexed table-operation bounds; a conservative bit implementation remains polynomial in N. Membership in the strict NAND tree class is not established by rectangle factorization alone.
5. With X empty, A=z and A_0=0, A_1=1. For F=NAND(z,B(z,Y)), F_0=1 masks B_0. This is information loss for the slice argument, not proof of nonuniqueness within the strict NAND class.

An independent second agent reached the same proof. It highlighted a useful boundary counterexample if the tree/no-repeated-leaf assumption is dropped: u=NAND(z,x), A=NAND(u,u) gives A_0=0. Thus a DAG with shared/tied fanins must not be treated as a read-once formula.

Scope qualification: once the local F table and the coordinate z are known, enumerating all labeled X/Y partitions is already inexpensive in truth-table complexity: at most 2^k=O(N) partitions, each with O(N) semantic table work, so O(N^2) overall before strict-formula recognition. The important outstanding obligations are identifying/extracting the local least-common-ancestor table, completing singleton cases, recognizing strict NAND factors, and identifying an internal reused signal z=T(W). Unfolding T repeats every leaf in W. Neither this answer nor the literature audit proves the full promised C(f)<=d reconstruction theorem, any general MCSP reduction, or P versus NP.