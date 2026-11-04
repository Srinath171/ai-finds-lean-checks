# Narrow NAND-coordinate check for the two-gate catalogue

The executed run checks only six scalar targets. It does not run the prepared 44-target, 16-coordinate campaign.

The complete finite catalogue in `low-cost-two-n5.json` has 22 input-permutation classes of pairs (f,g) with C(f)=2 and g a NAND of primary inputs. Five classes have J(f,g)=2. Six classes use four or five essential input coordinates across f and g; all six have J=3. The remaining classes fit within three inputs.

For the six larger-support cases, the driver examines only h=NAND, truth mask7. It independently composes each pair's joint witness with one additional NAND gate, removes unused input coordinates by identifying them with a retained variable, and renames the remaining coordinates to the lexicographically least truth mask. Constants are represented with one retained variable; no free constant signal is introduced. Every resulting circuit is checked by direct Boolean evaluation.

| Catalogue index | Variables | Canonical NAND(f,g) mask | At most3 gates | At most4 gates |
|---:|---:|---:|---|---|
| 1 | 4 | 36863 | UNSAT | SAT |
| 6 | 4 | 44782 | UNSAT | SAT |
| 7 | 4 | 35498 | UNSAT | SAT |
| 8 | 5 | 2298018040 | UNSAT | SAT |
| 11 | 4 | 44268 | UNSAT | SAT |
| 16 | 4 | 35064 | UNSAT | SAT |

All twelve queries completed without UNKNOWN. The narrow run took 1.649168 seconds. Its limits were 500 milliseconds per query, 300 seconds total, and twelve queries. Both the constructed upper witnesses and every SAT witness are retained in `results/low-cost-nand-six.json` and independently evaluated.

The lower bounds are Z3 UNSAT evidence from a Boolean one-hot encoding. A gate chooses exactly one unordered predecessor pair, including repeated fanins. Each gate has one Boolean truth value per input assignment, constrained by direct NAND clauses. The output chooses any input or computed gate. Duplicate and unused gates are permitted, so a bound of three includes every smaller circuit by unused-gate padding. This is not a formally checked UNSAT certificate or an independent-solver proof.

For any J=2 pair, appending NAND to its two outputs gives a scalar circuit of at most three gates. The artifact includes concrete upper witnesses for all five J=2 catalogue classes. Consequently the six larger-support classes are separated from every J=2 class at this single profile coordinate, subject to the recorded solver lower bounds. No claim about unrestricted C(f), a general scalarization algorithm, or P versus NP follows.

## Ordinary proof for the six larger-support cases

The following mathematical argument is separate from the finite Z3 evidence. It incorporates the [completed public Meta audit](provider-results/low-cost-support-audit-01-visible.md); its key counting and polarity steps were also checked independently. It is not a Lean formalization.

Prune a circuit for H=NAND(f,g) to the gates ancestral to its output. With k gates and e essential variables, the 2k gate-input slots contain at least k-1 occurrences of earlier gate outputs and at least e primary-input occurrences. Hence k >= e-1. Five essential variables require at least four gates.

For e=4 and k<=3, equality forces exactly three gates, four distinct primary leaves, and one use of each non-output gate. There are no repeated leaves, extra variables, repeated gate-output uses, or unused gates. Thus the circuit is a read-once NAND tree. Its only shapes have leaf depths (2,2,2,2) or (1,2,3,3). Because NAND reverses monotonicity at each level, their essential-variable polarity counts are respectively four positive/zero negative or one positive/three negative. Every leaf is unate: its direction cannot switch with the other inputs.

The two-gate classification gives exactly the following six patterns with support union greater than three. All displayed distinct letters denote distinct inputs, except the explicitly repeated z in NAND(z,z).

| f and g | H=NAND(f,g) | Obstruction to three gates |
|---|---|---|
| f=ab; g=NAND(z,t) | NOT(ab) OR zt | Four essential variables; two positive, two negative |
| f=NOT a OR b; g=NAND(z,t) | (a AND NOT b) OR zt | Four essential variables; three positive, one negative |
| f=ab OR NOT c; g=NAND(a,z) | (c AND NOT(ab)) OR az | Variable a is non-unate |
| f=ab OR NOT c; g=NAND(c,z) | c AND (NOT(ab) OR z) | Four essential variables; two positive, two negative |
| f=ab OR NOT c; g=NAND(z,z) | (c AND NOT(ab)) OR z | Four essential variables; two positive, two negative |
| f=ab OR NOT c; g=NAND(z,t) | (c AND NOT(ab)) OR zt | Five essential variables |

In the non-unate case, setting b=c=1,z=0 gives H=NOT a, while setting c=0,z=1 gives H=a. Essentiality of the other inputs follows by fixing the remaining inputs to isolate them; the independently evaluated truth tables verify each stated support. The four-variable polarity patterns exclude both read-once tree shapes, and the five-variable case is excluded by the slot count. Therefore all six H functions require more than three gates. Computing f in two, g in one, and the last NAND in one supplies four gates, proving C(H)=4 in these six patterns.

This ordinary proof covers the larger-support part of the restricted C(f)=2 analysis. Any complete conclusion about that subclass still needs the separate at-most-three-input record and its correctness argument. It does not formalize the full subclass in Lean or address arbitrary C(f).

## Prepared work that was not executed

The 22*16 profile entries reduce to 82 distinct scalar functions after removing unused inputs and quotienting by input permutations: four one-input classes, six two-input classes, 28 three-input classes, 34 four-input classes, and ten five-input classes. Existing verified small-input evidence covers 38 classes, leaving 44 new targets. Composed witnesses give upper bounds at most eight gates for all of them.

The module contains the bounded general-profile routine, but its command-line entrypoint now runs only the six-target NAND check. The full 44-target campaign was not executed. Cache validation and interval handling were exercised by focused tests. UNKNOWN keeps its lower/upper interval and is never promoted to an exact cost; an independently verified upper witness can establish a cost only when sufficient UNSAT evidence excludes every smaller bound.

## Reproduction and scope

```
python -B -m unittest continuation.test_low_cost_profiles -v
python -B -m continuation.low_cost_profiles
```

The second command reruns the twelve-query narrow check and overwrites its fixed public result file. The eleven focused tests passed in 2.949 seconds. They check all constructive upper witnesses, cached evidence chains, small-input boundaries against independent BFS, incremental output semantics, strict types, query/deadline caps, UNKNOWN preservation, and separation of intervals. The five J=2 upper witnesses may have fewer than three gates; only the bound at most three is needed.

The original `continuation/profile_sat.py`, all older sources, provider jobs, and budget ledgers are unchanged. No API or paid model call is made by this local checker.
