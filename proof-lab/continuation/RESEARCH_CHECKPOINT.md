# Mathematical research checkpoint

This checkpoint separates formal theorems, ordinary mathematical arguments, and bounded computational evidence. No novelty claim or P-versus-NP conclusion is made. The circuit model uses positive primary inputs, paid binary NAND gates, repeated fanins and shared wires; constants and negations are not free.

**1. Six concrete functions have exact NAND cost four in Lean.**

[SixCaseSupport.lean](SixCaseSupport.lean) proves a four-gate upper witness and excludes every circuit with at most three gates for each of six explicitly defined functions. The first five lower bounds use kernel-checked finite gate-list coverage connected to the actual circuit semantics; the sixth uses five essential inputs and the general dependency bound. See the [scope/proof note](SIX_CASE_SUPPORT.md) and [independent replay log](six-case-root-verification.txt).

These are six concrete theorems. The module does not formalize the global classification of all cost-two functions, its input-renaming/support transport, or the complete scalar-profile decoder.

**2. A global scalar-profile conclusion holds within the C(f)=2 subclass.**

Let g be a NAND of original primary inputs, including equal fanins, and let J(f,g) be their minimum shared-output cost. When C(f)=2, the labeled vector

    ( min(C(h(f,g)),4) : h is one of the sixteen Boolean binary maps )

determines whether J=2 or J=3. J=2 holds exactly for the five good signatures recorded in the [solver-free finite artifact](results/c2-truncated-n3.json), using that artifact's explicit h-index convention. The value 4 in this vector means at least four, not an exact cost claim.

This global restricted conclusion combines the [ordinary cost-two classification and dummy-input argument](LOW_COST_TWO.md), the [six-pattern support argument](LOW_COST_PROFILES.md), the concrete Lean cases above, and [complete enumeration through three gates on three inputs](c2_truncated_profile.py). The classifier reduces every pair to at most five retained input labels. Support at most three is covered by solver-free enumeration; each larger-support pattern has C(NAND(f,g))=4, whereas J=2 gives that coordinate at most three. The global classification and transport are ordinary mathematics, not an end-to-end Lean refinement. Nothing here settles scalar-profile determinacy for unrestricted C(f).

**3. Restricted reconstruction now has ordinary proofs, AI audits, and bounded code.**

- [Strict read-once reconstruction](READ_ONCE_NAND.md) uses exact signed-cofactor states and reconstructs a positive-leaf NAND tree precisely at the nonconstant essential-input boundary C(f)=d-1. The ordinary bound is poly(d)*6^d. See the [code](read_once_nand.py), [saved demo](results/read-once-nand-demo.json), and [independent Meta audit/review](read-once-dp-audit-01-review.md). Signs in table states do not grant free physical NOT gates.
- [Repeated-z reconstruction](REPEATED_Z_NAND.md) requires every ordinary variable once and z exactly twice. Its paired demands preserve syntactic variable sets, exact leaf counts, and whole-slice wildcards for masked information. The ordinary bound is poly(n)*8^n for n other variables. See the [code](repeated_z_nand.py), [Claude public audit](claude-reconstruction/visible-response.md), and [bounded exhaustive comparison](results/repeated-z-exhaustive-four-input.json).
- [Shared-subtree reconstruction](SPARSE_NAND_RECONSTRUCTION.md) combines those lemmas for a nonconstant complete table on d essential inputs, deciding C(f)<=d and returning an optimal witness on success. At d gates, the pruned optimum has one signal with two uses; its read-once ancestor subtree can be recovered by enumerating input subsets and grouping the table into two row types. Both row labelings are tested by actual strict-basis recognizers. The ordinary total bound is poly(d)*9^d. See the [assembler](sparse_nand_reconstruction.py), [demo](results/sparse-nand-reconstruction-demo.json), [exact Meta answer](results/shared-subtree-reconstruction-audit-01-answer.md), and [independent review](results/shared-subtree-reconstruction-audit-01-review.md). The external audit is explicitly conditional on the two subroutine lemmas, which have their own ordinary proofs and independent reviews.

The [rectangle helper](rectangle_recovery.py) and its [focused test record](results/rectangle-recovery-tests-20261104.txt) verify fixed-partition semantic factor recovery; that helper alone does not recognize NAND syntax or solve reconstruction. The read-once, repeated-z, and shared-subtree implementations have explicit finite/resource caps. A resource refusal is never a mathematical negative result. The reconstruction chain is not end-to-end Lean-formalized, and favorable AI verdicts are not formal certificates.

**Input length and the remaining P-versus-NP gap.**

Polynomial time in the full truth-table length N=2^d can still be exponential in d: for example, 9^d=N^(log_2 9). Reading that table already takes 2^d entries. These restricted table-input algorithms are not polynomial-time algorithms for arbitrary succinct NP inputs, and they do not solve unrestricted circuit minimization. The critical missing step for the user's P-versus-NP goal is a valid argument about unrestricted families and asymptotic complexity with the correct input encoding. More finite tests or favorable model verdicts do not supply that argument.

**Verification status and records.**

Assembler reciprocal actual-source peer review passed with the source hash unchanged. A new final integrated Python run passed all 475 tests; see the [combined replay log](python-reconstruction-verification.txt). The earlier combined run with a Windows file-replacement error and its later isolated passing recheck remain separate historical results. No new combined Lean replay is claimed here. Aggregate verification and billing records remain in the authoritative files below.

Use the authoritative [verification manifest](../results/verification.json), [provider receipt summary](provider-results/completed-summary.json), and [budget snapshot](provider-results/budget-snapshot.json) for recorded counts, source hashes, outcomes, timestamps, and spending. Consult each record's own status and timestamp; a historical snapshot must not be read as including later settlements.