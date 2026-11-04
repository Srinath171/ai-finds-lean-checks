Public mathematical audit. Please aggressively check this one concrete proposed lemma; return a concise visible verdict with complete corrected proof or an explicit counterexample. Do not spend the response on broad PvsNP strategy.

Strict unit-cost NAND DAGs, repeated fanins/freefanout, original inputs free, no free constants/negations. C(f)=2, g=NAND of two original inputs, J shared-output cost. Proposed lemma: if the union of essential supports of f and g has more than3 variables, then C(NAND(f,g))=4. A generic f2+g1+outputNAND1 gives upper4. If true it closes the new-arity gap for C2 scalarprofile determinacy: every J2pair has NANDscalarcost≤3, so any same16cost-profile/differentJ collision must already occur on≤3inputs. It does not solve higherC or PvsNP.

Audited C2 classification, up to inputpermutation: 1; a ANDb (distinct); NOTa ORb (distinct); ab ORNOTc (all3distinct). A minimal2gate circuit's first gate u is originalNAND, and last is NAND(u,u) orNAND(u,primary); expanding overlaps gives these4forms. A constant target cannot have supportunion>3. Therefore outside the≤3input cases, the six canonical cases for f andg are:
1 f=ab, g=NAND(z,t), all4distinct.
2 f=NOTa ORb, g=NAND(z,t), all4distinct.
3 f=ab ORNOTc, g=NAND(a,z), all4distinct (a andb symmetric).
4 f=ab ORNOTc, g=NAND(c,z), all4distinct.
5 f=ab ORNOTc, g=NAND(z,z), all4distinct.
6 f=ab ORNOTc, g=NAND(z,t), all5distinct.

Proposed lowerbounds: Any3gate function with4essential inputs must use all3gates in a connected read-once NAND tree, without repeated leaves/fanout/unusedinputs, by input-slot counting. Such a4leaf tree has only balanced and comb shapes. With uninverted primary leaves their unique unate polarity counts are respectively4positive/0negative and1positive/3negative. Case1 scalarH=NOTab ORzt has2positive/2negative. Case2 H=(a ANDNOTb) ORzt has3positive/1negative. Case4 H=c AND(NOTab ORz) andcase5 H=(c ANDNOTab) ORz each have2positive/2negative. Case3 H=(c ANDNOTab) ORaz is nonunate in a (check actualassignments); all4variables must be essential. Case6 has5essentialvariables, so3gatescannotcomputeit. All give lower4. Verify every expression, essentiality, polarity, tree-completeness claim, and possibility of irrelevant originalinputs/syntacticcancellation in a minimal circuit. Distinguish semanticessential support from mere syntax. Do not accept a free inversion, hidden constant, formula-vs-DAG substitution, or missing case.

If the proof passes, state exactly what it establishes when combined with finite three-input checks; those checks currently use audited Z3 UNSAT evidence plus independently evaluated SAT witnesses, not a Lean-certified UNSAT proof. UniversalC2 profiledeterminacy is conditional on correctness of that remaining finite record; the proposed supportlemma itself is ordinary mathematics. No novelty claim is requested.
