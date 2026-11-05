# Primary literature note: strict NAND, read-once, and one reused signal

Prepared 2026-11-04. This is a limited source audit, not a novelty claim. No source located in this audit directly proves polynomial-in-truth-table-length optimal reconstruction for every strict binary NAND circuit with d essential inputs and at most d gates.

1. Angluin, Hellerstein, Karpinski, Learning Read-Once Formulas with Queries (technical report; later JACM 1993), Theorem 9.
https://theory.cs.uni-bonn.de/ftp/reports/cs-reports/1985-1989/8535-CS.pdf
The ordinary AND/OR/NOT read-once learning result uses O(d^4) computation, O(d^3) membership queries, and O(d) equivalence queries. A complete N=2^d table can answer membership queries and simulate an equivalence query by scanning the table; O(d^4+d^2 N) is a safe resulting bound. Negated literals are permitted. This is a read-once identification theorem, not an exact strict-NAND gate-count theorem, and it does not cover a shared internal signal.

2. Netanel Raviv, Truth Table Minimization of Computational Models, arXiv:1306.3766, Corollary 3.4; Definition 3.15, Theorem 3.12 and Corollary 3.7; section 3.2.5.
https://arxiv.org/pdf/1306.3766
Corollary 3.4 gives polynomial-in-2^n minimization for ordinary Boolean/arithmetic read-once formulas. The later unate-order-2 result is over AND/OR formulas with leaf negations, counts leaves, and imposes a specific depth condition on repeated-occurrence induced subformulas. It is not a theorem for arbitrary read-twice formulas or arbitrary one-shared-signal NAND DAGs. Section 3.2.5 distinguishes paying for NOT gates; its positive result has an explicit skeleton-preserving restriction. It must not be cited as unrestricted paid-NOT or strict-NAND minimization.

Structural caution: if a circuit reuses an internal signal T(W), unfolding the DAG repeats every leaf in that subtree. Thus a theorem allowing one repeated primary variable does not cover this circuit class without a separate reduction.

Narrow independent lemma prepared for review: a strict read-once NAND formula A(z,X), with X nonempty and all leaves distinct, has no identically-zero cofactor in z. Its only possible constant cofactor is 1 at z=0 when z is a root child. Consequently, at a repeated-z least common ancestor NAND(A(z,X),B(z,Y)), when X and Y are nonempty and disjoint, every fixed-z zero set is a nonempty rectangle. Its projections uniquely recover both factors for a specified partition. This is an elementary local factorization lemma, not a complete reconstruction algorithm. Singleton branches, ancestors, unknown partition, strict-NAND recognition, and identifying T(W) remain separate obligations.

Additional exact shared-output sources from the earlier audit:
- Reichl, Slivovsky, Szeider, eSLIM (SAT 2024), section 3.2, pages 23:5-6: relational specifications R:B^n -> nonempty subsets of B^m and exact replacement constraints. https://drops.dagstuhl.de/storage/00lipics/lipics-vol305-sat2024/LIPIcs.SAT.2024.23/LIPIcs.SAT.2024.23.pdf . Such relations express a helper-graph partial specification, but they are not ordinary total single-output MCSP and use different gate conventions.
- Haaswijk, Soeken, Mishchenko, De Micheli, SAT-Based Exact Synthesis (TCAD 2020), sections II-III: exact shared-DAG synthesis by first satisfiable gate count in the paper's chain model. https://si2.epfl.ch/~demichel/publications/archive/2019/Haaswijk-SAT-based%20Exact.pdf . Constants, complemented outputs, normalized gates, and distinct-fanin encodings prevent transferring its objective unchanged to strict NAND.
No theorem was found that the sixteen scalar costs C(h(f,g)) determine the exact shared two-output NAND cost, including when g has cost one. Failure to find one is not proof that none exists.