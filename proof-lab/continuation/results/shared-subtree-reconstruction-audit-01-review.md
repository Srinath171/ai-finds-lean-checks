# Independent review: shared-subtree-reconstruction-audit-01

Outcome: PASS for the outer mathematical reduction, conditional on the stated soundness, completeness, reconstruction, and runtime lemmas RO and TWICE. This does not independently re-prove TWICE, certify an unbounded implementation, establish novelty, or imply a result about general MCSP or P versus NP.

The single guarded Muse Wonder MAX job finished successfully: phase TERMINAL, finished true, incomplete false, usage settled, cost USD 0.443636. It used 1484 input tokens, 21885 output tokens including 19401 reasoning tokens, and 23369 total tokens. The guard reports 14 HTTP requests including submission/polling; this is one model job. Exec session 42652 was fully collected with exit code 0. No further paid calls were made.

The companion answer file contains the exact state.visible_text with no title or provenance prefix. Source state: continuation/jobs/shared-subtree-reconstruction-audit-01/state.json. Public prompt: continuation/prompts/shared-subtree-reconstruction-audit-01.md.

Independent proof assessment:

1. Structure. For a pruned circuit using the d essential primaries and s gates, the total nonoutput-outdegree surplus is s-d+1, with repeated fanin occurrences counted separately. At s=d-1 all nonoutput vertices have one use, yielding a strict read-once NAND tree. At s=d exactly one nonoutput signal q has two uses. Every proper ancestor of q has its sole outgoing edge on a path to q, so it cannot leak outside the q ancestor set. That set is a read-once tree on a nonempty W and has |W|-1 gates. Collapsing q and duplicating only its two uses yields an outside formula with z twice and Y once, hence |Y|+1 gates.

2. Necessary wording qualification. If q is an internal gate, all W primaries have no outside uses. If q is itself a primary, W={q}, the ancestor tree is just that leaf, and q's two outside uses are precisely the two z occurrences. The statement that every W variable is confined to the subtree must explicitly allow this primary-signal boundary case.

3. Row recovery. The genuine decomposition gives at most two row functions over Y. Surjectivity of the read-once q makes both q-values occur, and essentiality of nonempty W forces the two H slices to differ. The row classifier and both H slices are then read directly from f; trying both labelings includes the original q/H. No arbitrary hidden truth table is guessed.

4. Interface strengthening for implementation. For ANY candidate W whose rows have exactly two types, the exact factorization f(w,y)=H(q(w),y) makes q essential in every W coordinate: if changing that coordinate never changes q, it cannot change f. Likewise H is essential in every Y coordinate, and its two distinct slices make z essential. Thus a read-once recognizer that canonically discards dummy inputs cannot silently shorten the required q tree when f has the promised full essential support. TWICE must still preserve its exact syntactic leaf multiset.

5. Cost and negations. A successful q-tree and H-formula compose to exactly (|W|-1)+(|Y|+1)=d paid NAND gates, sharing q only. Row relabeling complements the candidate classifier semantically, but that exact classifier must pass RO and the exact slice-swapped H must pass TWICE. This grants no free physical NOT. The initial RO test and the d-1 lower bound make a later d-gate witness optimal.

6. Boundaries. For d=1, x has cost0 and NOT x is recovered using q=x and H=NAND(z,z), cost1. When W is all inputs, Y is empty and TWICE's exact two-z requirement permits only the one-gate NOT, not the zero-gate identity. Reused primaries and equal fanins are included by edge multiplicity. Constants are outside the stated nonconstant target domain and no free constants enter constructions. Ambient dummy inputs can be replaced by a retained essential variable before pruning, preserving f and not increasing cost.

7. Runtime. For each W, comparison with at most two explicit representative rows costs poly(d)*2^d. Across W this is poly(d)*4^d. RO calls sum to poly(d)*7^d and TWICE calls to poly(d)*9^d. The initial RO call is dominated. These are uniform ordinary table-algorithm bounds conditional on the subroutine lemmas, not a claim that fixed-size/capped executables decide all inputs. A bounded assembler must propagate RESOURCE_LIMIT rather than convert it into mathematical rejection.

No fatal gap was found in the outer reduction. The result remains an ordinary mathematical proof plus independent AI review, not end-to-end proof-assistant formalization.