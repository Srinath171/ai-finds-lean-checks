# What the sixteen scalar complexity values currently certify

Status: independently AI-reviewed mathematics, not Lean-formalized or human-reviewed. Research stopped on the parent's instruction; this note records only results already developed. No general counterexample or general determinacy theorem is established. No model/API calls or computational profile search were performed by this reviewer.

## 1. Model and open question

Use unit-cost two-input NAND DAGs, repeated fanins, free primary wires and output selectors, and no free constants or negations. Let n>=1, g=NAND(x_i,x_j), and let

    profile(f,g) = ( C(h(f,g)) : h is one of the sixteen Boolean binary maps ).

The order of the sixteen labeled maps is fixed; this is a labeled vector, not an unordered multiset. Let c=C(f), and let J be the minimum shared-DAG cost supplying both f and g. Always

    c <= J <= c+1, and J>=1.

The question is whether the profile determines which of c,c+1 occurs, for this restricted g. The reported complete two-input check found no collision with different J, but that is finite evidence, not a proof for arbitrary n. Input permutations and unused-input extensions preserve both the profile and J, so they do not produce a counterexample.

## 2. A rigorous profile lower bound

For each binary map h, define mu(h) to be its NAND complexity when its two arguments are independent free primary signals. A joint circuit of size J supplies the two arguments, so appending an optimal mu(h)-gate circuit computes h(f,g). Therefore

    L(profile) := max_h [ C(h(f,g)) - mu(h) ] <= J.

In particular, the two projections h(a,b)=a,b have mu=0, so L>=max(c,1). Consequently

    L>c implies J=c+1.

This is a sufficient certificate of the extra gate, not a proved complete test. If every entry satisfies C(h(f,g))<=c+mu(h), the inequality alone leaves J unresolved. Explicit implementation upper bounds in place of mu(h) also yield valid, possibly weaker lower bounds. All costs must use the same paid-constant NAND model.

## 3. Rigorous upper certificates from reversible scalar combinations

Independent optimal circuits for the following scalar functions, followed by a direct one-gate computation of g and the indicated decoder, give

    J <= U := min( c+1,
                  C(NOT f)+2,
                  C(f XOR g)+5,
                  C(XNOR(f,g))+6 ).

The second term uses one NOT for f and one NAND for g. The third uses g plus a four-NAND XOR decoder. The fourth uses g plus a five-NAND XNOR decoder. These are existence upper bounds; they assume neither sharing between the scalar circuit and g nor an oracle returning a witness.

If i=j, then g=NOT x_i, and XNOR(f,g)=f XOR x_i. The last term improves to C(XNOR(f,g))+5, using the primary x_i in the four-gate XOR decoder while retaining a one-gate output g.

Thus U<=c certifies J=c. Together, L and U can certify some profiles' answers without a direct-sum assumption. Their completeness has not been established.

## 4. The profile determines J for every n when c<=1

If c=0, f is a primary projection. Since g is not a projection, exactly one gate is needed jointly: J=1.

Suppose c=1. Then f itself is a NAND of two original primary inputs, possibly repeated. Put

    p=C(NOT f), q=C(NOT g), r=C(f AND g).

The labeled profile contains all three values. Each of p,q belongs to {0,2}: a repeated-input NAND is a negated primary input and its complement is a zero-gate projection; a distinct-input NAND has an AND complement of exact cost two. The latter is neither a projection nor a one-NAND function, and its usual two-gate construction gives the upper bound.

The exact formula is

    J=1 iff p=q and r=1;
    otherwise J=2.

Proof: two distinct noninput output functions require two distinct gates, while two direct NANDs always suffice. Hence J=1 exactly when f=g. If p!=q, their repeated/distinct types differ and f!=g.

If both are repeated-input NANDs, different functions are NOT x_a and NOT x_b with a!=b. Their conjunction is NOR of those two inputs, which is not a one-gate NAND or a projection; thus r!=1. If they coincide, r=C(f)=1.

If both have distinct fanins but different unordered input pairs, their conjunction depends essentially on the union of those pairs, which has at least three variables. For a shared-variable pair it has the form NOT x OR (NOT y AND NOT z), depending on all three; disjoint pairs give four essential variables. A single NAND depends on at most two inputs, so again r!=1. Equal pairs give f=g and r=1. This proves the formula uniformly over every n, not merely on the two-input dataset.

Therefore any counterexample profile collision with different J must have c>=2. This restriction does not prove that such a collision exists.

## 5. Constant targets: a conditional structural classification

If f is known from its table to be constant one or constant zero, then J=c when g is a negated primary input, and J=c+1 when g has distinct fanins. The profile distinguishes these two g types by q=C(NOT g)=0 versus 2.

For constant one, c=2. A negated-input g is used directly in NAND(x_i,NOT x_i)=1. A distinct-fanin g cannot occur in a two-gate constant-one circuit: its six possible next NAND functions contain no constant one, and a first gate cannot already be one. Thus the joint cost is three.

For constant zero, c=3. Any final NAND computing zero must have both fanin functions identically one. In a three-gate circuit the constant-one wire must therefore occur by gate two, forcing gate one to be a negated primary input. A distinct-fanin g cannot occur among those three required functions. A separate g plus the usual three-gate zero construction gives joint cost four; a negated-input g fits the three-gate construction.

This is a statement conditional on knowing f is constant. It does not assert that its entire labeled profile can never collide with the profile of a nonconstant target.

## 6. Remaining scope

The only universal classifications proved here are the displayed bounds and the low-cost/conditional subclasses. A shared witness might exploit an internal g-wire in ways not forced by an individual scalar optimum; that observation is motivation for the question, not a proof that the sixteen values lose the needed information. Conversely, the absence of a collision in the reported small search is not a reason to assert a universal decoder.

The case c>=2 remains unresolved in this analysis. No unconditional impossibility theorem, exact general scalarization, MCSP lower bound, novelty result, or P-versus-NP solution is claimed. Further research/model work was stopped rather than extended after the parent's stop instruction.
