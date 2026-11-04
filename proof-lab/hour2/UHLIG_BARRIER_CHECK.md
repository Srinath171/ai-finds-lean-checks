# Uhlig mass production: primary-source and NAND-constant check

Status: bounded source check and independent AI reasoning, not Lean-formalized or human-reviewed. **The precise original theorem specialized to unit-cost NAND has not been verified here. In particular, this check does not establish a barrier for every fixed t>=2.** No scalarization, circuit lower bound, novelty claim, or P-versus-NP result follows.

## 1. What was actually read

The saved regular-Claude critique explicitly recalled Uhlig in the full binary basis and itself left the NAND-constant transfer unverified. Its all-fixed-t>=2 suggestion therefore required an independent source check.

The original [Uhlig 1992 chapter publisher page](https://www.cambridge.org/core/books/boolean-function-complexity/networks-computing-boolean-functions-for-multiple-input-values/0C17F7D841F904EA91FD3E3133A85B70), *Networks Computing Boolean Functions for Multiple Input Values*, pp.165--173, DOI 10.1017/CBO9780511526633.013, exposes its abstract and introductory model. That model allows an arbitrary complete gate set G with positive gate costs and defines total circuit cost as the sum. This permits NAND as a gate-set example at the model level. The full quantitative theorem, its leading coefficient and its detailed constant/negation conventions were not exposed by that page. They must not be inferred solely from the introduction.

The [original 1974 English article publisher page](https://link.springer.com/article/10.1007/BF01152835), *On the synthesis of self-correcting schemes from functional elements with a small number of reliable elements*, identifies the paper and gives only a reliability-synthesis abstract. Its full text was subscription-limited in this check; the linked MathNet route was inaccessible. No paywall or access control was bypassed.

For comparison, [Kretschmer's 2023 research paper, Section1 and its proof overview](https://arxiv.org/html/2212.14399v2) explicitly describes Uhlig's classical mass-production result and the two-copy construction: arbitrary Boolean f, r=2^{o(n/log n)} independent input blocks, and O(2^n/n) total gates with an unchanged leading coefficient as r grows. This is a later account inside a primary research paper, not a substitute for reading the precise original basis theorem. Its quantum CNOT theorems are not NAND bounds and are not used here.

## 2. The quantifiers and the normalization that matter

The reported result concerns a shared circuit computing the vector

    f^r(x^1,...,x^r) = (f(x^1),...,f(x^r))

on independent inputs. Every fixed r is within the reported subexponential range. The quoted benchmark is worst-case one-copy Shannon complexity, not necessarily the actual complexity C(f) of each particular easy f. A contradiction to a universal forcing lemma must therefore choose sufficiently hard f and control both bases' leading constants.

For the project model, every NAND costs one, primary wires and output selection are free, repeated fanins are allowed, and constants/negations are not supplied for free. A statement in another complete basis does not automatically have leading coefficient one in this model.

## 3. A valid conservative basis conversion

A literal arbitrary-binary-gate replacement cannot be advertised as four NAND gates: standalone XNOR requires five in this model. Nevertheless, a whole circuit of S arbitrary binary gates and r outputs can be converted to at most

    4S + O(r) + O(1)

NAND gates by polarity tracking. Represent every internal signal either by its desired Boolean value or by its complement and record that tag. Absorb input tags into the truth table of each next binary gate. Up to output complementation, every binary function is a constant, literal, AND-type function, or parity. Literals can be wires with a tag, AND-type functions need at most three NANDs after choosing output polarity, and parity needs four. Correct final output polarities with at most r paid NOT gates. A shared constant can be generated from one primary input by a constant number of paid NAND gates. This gives a valid constant-factor conversion without pretending internal negations are free.

It does not preserve the leading constant exactly. The O(r) and constant costs are negligible for a fixed r when compared with 2^n/n, but the factor four is not.

## 4. Hard NAND functions with the needed comparison scale

A self-contained counting bound gives a one-copy NAND lower scale (1-o(1))*2^n/n. Prune a circuit to its s gates reachable from the output, traverse the two fanin positions of each gate depth first, and allocate a gate identifier on first visit. Of the 2s positions, s-1 introduce a new gate; the remaining s+1 are references to a known gate or primary input. Encoding the introduction/reference pattern in at most 2^(2s) ways and each reference using at most n+s labels overcounts all such circuits. Thus the number of functions with at most s gates is at most

    (s+1) * 2^(2s) * (n+s)^(s+1) + n,

where the final term covers zero-gate projections. Invalid decoded cycles only overcount. For s=(1-epsilon)*2^n/n, the base-two logarithm of this expression is at most (1-epsilon+o(1))*2^n. Hence, for every fixed epsilon>0 and sufficiently large n, some f has C_NAND(f)>s. This is an existence/counting argument, not an explicit hard NP language.

## 5. Qualified consequence for Muse's forcing lemma

Here is a precise **conditional** implication, keeping the unverified source specialization visible. Assume a binary-basis mass-production bound

    for every fixed t and every n-bit f:
    C_B2(f^t) <= (1+o(1))*2^n/n,

with the asymptotic leading coefficient independent of fixed t. Then polarity conversion, t direct one-gate copies of g, and the fixed D-gate Phi circuit give

    C_NAND(H_Phi) <= (4+o(1))*2^n/n + O(t) + D.

Choose NAND-hard f from Section4. Since J(f,g)>=C_NAND(f), Muse's proposed universal lower bound would demand

    C_NAND(H_Phi) >= t J(f,g)+A
                     >= (t-o(1))*2^n/n + A.

For every fixed t>4 these inequalities conflict for large n, independently of the constant A. This yields a conditional obstruction for t>=5. It gives **no contradiction for t=2,3,4** with these constants, and no conclusion for t=1. More generally, a mass-production coefficient K and simulation factor kappa only yield this comparison when t>kappa*K. An unspecified O(2^n/n) is not an all-t>=2 refutation.

To exclude every fixed t>=2 by this route, one would need a verified unit-NAND mass-production theorem with leading coefficient matching the unit-NAND one-copy hard scale closely enough (or another sharper comparison). The original complete-basis introduction makes such a specialization plausible but does not prove it. This check leaves that exact source theorem and its constants **unverified**, rather than silently upgrading the model's recollection.

## 6. Current conclusion

Mass production is a documented and relevant warning against assuming circuit direct-sum lower bounds. The original quantitative NAND specialization needed for Claude's strongest claim was not obtained from the accessible primary text in this bounded check. The all-fixed-t>=2 barrier must therefore remain qualified. Even a verified failure of the constant-copy forcing family would not exclude adaptive oracle reductions, different scalarizations, or settle P versus NP.
