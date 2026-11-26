# Simultaneous stages and short descriptions

Section 5 combines two kinds of choice. The global sequence of blocks may be
chosen classically. Within each fixed stage, a single ordinary program must
reconstruct the final affine equations from a small numerical input. A literal
syndrome would cost one bit per equation and exhaust the saving needed by the
affine-description test.

This note explains the checked candidate estimates, finite rational
statistics, bounded-advice horizon search, computed syndrome, fixed
reconstruction program, and global recursion. These supply the assumption-free
separation theorem for the repository's total computable-real strategy convention.

## Fixed data and variable input

At stage `n`, the protected strategies are the first `n + 1` members of a
countable enumeration of all total computable-real betting strategies. Their
proved normalizations supply rational signed wagers. The enumeration is
classical; no effective enumeration of total programs is used.

Before varying the trial rank, the program header fixes the previous affine
codes, finite protected strategy list, positive rational parameters, and the
actual program supplied by the computable-pool theorem. Its variable input is
precisely

$$
\langle r,\langle q,b\rangle\rangle,
$$

where `r` is the trial rank, `q` is a candidate-list position, and `b` is bounded
integer advice about a limiting first-drop probability. The pool, matrix,
horizon, syndrome, and certificate are computed internally.

`StageReconstruction.exists_fixed_program` places the existential program
quantifier before all three variable inputs. Rank-dependent data cannot be
hidden in this header.

## Selecting one candidate

For trial rank `r`, the paper's parameters are

$$
M=r^8,\qquad m=r^2,\qquad J=M^3=r^{24}.
$$

Lemma 3 supplies a nodup pool of `M` actual positions. Lemma 4 supplies an
executable list of `J` supported full-rank matrices. List positions retain
multiplicities, including repeated entries.

For each normalized strategy, let `A_i(S)` be the all-time sum of absolute
wagers placed in `S`. Freshness and the square budget imply, pointwise,

$$
A_i(G)\le\sqrt{M/2}.
$$

The incidence bound then gives, for any probability input law `P`,

$$
\frac1J\sum_q\mathbb E_P A_i(S_q)
\le\frac{2m}{M}\sqrt{\frac M2}
=\frac{\sqrt2}{r^2}.
$$

`StageWeights` proves both this estimate and agreement of the position-based
sum with the actual sum over adaptive query times.

For each complete answer sequence, the same never-read pool mask is tested
against the whole candidate list. Outside the low pool exception, the verifier
bounds the fraction of candidates losing rank on that mask. Full rank on
never-read columns prevents every finite rank drop. Integrating the candidate
count yields

$$
\frac1J\sum_q\kappa(L_i\cap\{q\text{ has a rank drop}\})\le\eta+\theta.
$$

The infinite mask is used only in this existence proof. Selecting a separate
candidate for each mask would not establish the required probability bound.

`StageChoice` adds the wager and rank scores before selecting one position.
Conditioning on `K` old equations costs at most `2^K` relative to fair coin on
answer space. The same candidate therefore controls all protected strategies
and all earlier stage laws.

`StagePreHorizon.exists_fixed_partitions_eventual_candidates` proves this
with actual pool-program and sparse-list-search outputs. The Borel partitions
are fixed first; positive rational parameters and one pool program precede
the varying rank. All candidate estimates hold for every later syndrome.

## Exact finite probabilities

`StageFiniteScan` computes an input depth covering every query on every
adaptive branch through a finite horizon, together with every old affine-code
coordinate. It simulates the scan on every binary word of that depth and
counts satisfying assignments with exact rational arithmetic.

For a finite statistic `f`, the conditional value is

$$
\frac{\sum_{\sigma:\,\text{old equations hold}}f(\sigma)}
{\#\{\sigma:\,\text{old equations hold}\}}.
$$

Lean identifies this quotient with the real integral under the actual
conditioned fair-coin law. The identity includes empty conditions, where both
the conditional measure and the field quotient vanish. Disjoint full-rank
previous blocks guarantee positivity when a probability law is needed.

`StageRankCode` implements finite unread masks and exact full-, zero-, drop-,
and partial-rank tests. Distinguishing zero, full, and intermediate rank is
sufficient; the verifier needs no general numerical rank computation.
`StageRankProbability` computes the actual rational sequences

$$
u(t)=\sum_{i\le n}P(0<R_i(t)<r),\qquad
v(t)=\sum_{i\le n}P(T_i\le t).
$$

Their real casts are proved equal to those event probabilities. No limiting
rank or infinite never-read predicate occurs in their computation.

## Bounded advice for the horizon

Remaining rank stabilizes on every input. Bounded convergence gives the limit
of the partial-rank probabilities. Eventual partial rank forces either a
high-part missed pool position or a low-part drop, so the selected candidate
gives `u∞ < 2ε`. Increasing first-drop events give `v(t) → v∞ ≤ n + 1`.

The advice is

$$
b=\lfloor v_\infty/\varepsilon\rfloor
\le\lfloor(n+1)/\varepsilon\rfloor.
$$

This bound is independent of the trial rank. The actual partial-recursive
search returns the first `V` with

$$
u(V)<3\varepsilon,\qquad v(V)>(b-1)\varepsilon.
$$

Subtraction occurs after casting `b` to the rationals. When `b=0`, the threshold
is `-ε`; natural-number truncated subtraction would instead give zero and
could prevent termination when `v∞=0`. This is a necessary Lean encoding detail,
not a change to the usual mathematical interpretation of the paper.

The analytic and computational horizon modules prove termination, leastness,
and the actual tail identity

$$
v_\infty-v(V)=\sum_{i\le n}P(V<T_i<\infty)<2\varepsilon.
$$

The stopping-transcript identity preserves this first-drop tail under every
syndrome of the new block.

## Computing the syndrome

The finite objective uses the truncated total support wager `A_i(S;V)` in
place of the smaller rank-drop-only wager `W_i(V)`. This strengthens the
objective while preserving its budget:

$$
W_i(V)\le A_i(S;V)\le A_i(S).
$$

The old-law expectation of the total truncated wager is below `ε`, and the
horizon makes the partial-rank mass below `3ε`. Every syndrome of a fresh
full-rank matrix has old-law probability `2^-r`. Thus the average of the new
conditional objectives over all `2^r` syndromes is exactly the old objective.

`StageSyndromeObjective` computes those rational conditional objectives and
chooses a minimum, retaining the first minimizer in the binary-word
enumeration. It proves minimization of the actual integral over every
mathematical syndrome vector. The resulting objective is below `4ε` and
dominates the required early-drop wager plus partial-rank mass.
`StageHorizonChoiceBounds` gives the precise ENNReal estimates used by
`StageEstimates`, together with the first-drop tail estimate.

## Certified output and the length budget

The selected matrix initially uses pool indices; the affine decoder uses
actual input coordinates and a right-inverse certificate. `StageCandidateCode`
computes the desired finite truth table by reading input words at the concrete
pool positions. `StageCodeSearch` enumerates finite affine codes until the
certificate, required rank, and exact truth table all check. Bounded
affine-code coverage proves termination. The resulting event is exactly the
selected block event.

Runtime is immaterial here. This exhaustive procedure is an ordinary
partial-recursive computation whose variable input is short; it need not be
efficient.

For `q<r^24` and bounded `b≤B`, the actual pairing satisfies

$$
\operatorname{size}\langle r,\langle q,b\rangle\rangle
\le96\operatorname{size}(r)+4\operatorname{size}(B)+4.
$$

`StageProgramLength` consequently gives `2|p|+n+1≤r` for every sufficiently
large rank, uniformly over all allowed advice. `StagePrepared` fixes the
reconstruction program first, then chooses a rank satisfying both the
eventual candidate estimates and this eventual description budget.

## Global assembly and entry points

Later supports must avoid the old supports and every position that a
previously protected scan could query on any branch through its assigned
horizon. `StageCandidateBridge` supplies both the exact representation bridge
and the support representation needed for these cutoffs.
`StageRecursion.History` stores a finite history as an infinite sequence
padded by empty rank-zero blocks. Its cutoff includes every old support and
every all-branch query bound for each previously protected pair of a stage
and a strategy.

`StageRecursion` builds these histories by dependent recursion. Prefix
coherence identifies every earlier finite-stage law with the corresponding
law of the infinite diagonal sequence. Later blocks avoid every protected
finite horizon. For strategy `i`, all required estimates hold from stage `i`
onward. In the later-low-drop estimate for a stage `j` and a later block `k`,
the construction uses the earlier-law bound with `a = j + 1 ≤ k`; controlling
only the immediate preceding law would not suffice.

`StageOneStep` connects the actual evaluated program to its selected block
and all four probability bounds. `StageConstruction` obtains fixed partitions
admitting that extension after every old prefix and beyond every requested
cutoff. It therefore removes the explicit extension premise of the general
recursion theorem.

Finally, `StageEnumeration` chooses a surjective enumeration of the actual
countable total-strategy type. `Separation` applies the exact-affine-program
reduction to the resulting sequence. Its existence theorem has no
construction, program-execution, description-length, or effectiveness hypothesis.

| Module | Role |
| --- | --- |
| [StagePreHorizon](../Klr/StagePreHorizon.lean) | Actual eventual candidates, with partitions and program parameters fixed first |
| [StageRankProbability](../Klr/StageRankProbability.lean) | Computable horizon statistics with exact measure meaning |
| [StageHorizonComputable](../Klr/StageHorizonComputable.lean) | Least-horizon search using bounded integer advice |
| [StageSyndromeObjective](../Klr/StageSyndromeObjective.lean) | Exact objective, computed minimizer, certified final output |
| [StageHorizonChoiceBounds](../Klr/StageHorizonChoiceBounds.lean) | Actual early and tail estimates for the chosen syndrome |
| [StageReconstruction](../Klr/StageReconstruction.lean) | One fixed program with only rank and two advice values as input |
| [StageProgramLength](../Klr/StageProgramLength.lean) | Uniform budget for the explicit nested-pair input |
| [StagePrepared](../Klr/StagePrepared.lean) | Rank selected after the fixed program, with all bounds simultaneously |
| [StageOneStep](../Klr/StageOneStep.lean) | Actual coded output and every one-stage estimate |
| [StageRecursion](../Klr/StageRecursion.lean) | Coherent histories, horizon preservation, and the infinite sequence |
| [StageConstruction](../Klr/StageConstruction.lean) | The extension premise fully discharged |
| [Separation](../Klr/Separation.lean) | Unconditional separation and proper inclusion for the defined strategy convention |

No stage selection or reconstruction property is introduced as an axiom.
The only separate scope obligation discussed in the README is the bridge
from general partial computable-real source programs to the total-strategy
convention. It is not a premise of the proved theorem.
