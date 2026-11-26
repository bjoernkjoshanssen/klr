# Audit and formalization roadmap

## Scope and current conclusion

This document concerns the supplied version 1 of Chenghua Liu and Boning Meng,
*Separating Kolmogorov–Loveland randomness from Martin-Löf randomness*,
arXiv:2611.31004, dated 23 November 2026. Page references below are the printed
page numbers of that version.

The initial informal review found **no mathematical error requiring correction**.
In particular, the normalization, the use of non-effective finite advice, and
the transfer from finite-stage measures to the final measure survive the
checks described below. This conclusion is limited: the proof has not been
formalized in full, and the most substantial construction lemmas remain open
formalization tasks.

The repository contains proved foundations and intermediate lemmas, rather
than a theorem whose missing arguments are hidden in hypotheses or axioms.
The README and individual module headers record the scope of each component.
There is currently no unconditional Lean theorem asserting existence of a
KL-random sequence that is not ML random. The final probabilistic reduction is
checked, with the construction's concrete finite-stage estimates and effective
description-cover obligations left explicit.

## Definitions and their verification

### Cantor space and effective open sets

We use `ℕ → Bool` for Cantor space and `List Bool` for finite strings. A cylinder
contains exactly the infinite extensions of a finite string. The fair-coin
measure is constructed as the infinite product of Bernoulli measures of
parameter `1/2`; it is not a measure supplied as an unspecified parameter.
The cylinder formula is proved:

\[
\lambda([s])=2^{-|s|}.
\]

An effectively open class is a union of cylinders indexed by a predicate
satisfying Mathlib's `REPred`. This is genuine partial-recursive effectivity.
Uniform effectiveness is represented by one c.e. predicate on pairs `(n,s)`.

A `MartinLofTest` carries one program recognizing cylinder codes at all levels and a proof of the
measure bound. We prove that every uniformly c.e. family has such a code, then
prove equivalence with the customary set-based definition. Countability of
programs yields countability of tests. The nullity of each failure set gives
almost-everywhere ML randomness and existence of ML-random sequences.

As a check that the definition also excludes the expected examples, the
development proves that a computable sequence fails its uniform prefix test
`[X ↾ n]` and therefore cannot be ML random.

The library numbers test levels from zero. This does not alter randomness:
discarding the zeroth level gives the paper's positive-index convention, and
inserting the whole space as level zero gives the reverse conversion.

### Betting strategies

A scan rule is a total computable map from finite transcripts to input positions.
Its freshness condition applies to every finite branch: a query at a transcript
must differ from the queries at all its proper prefixes. Consequently, the
actual run on every input queries each position at most once.

Capital functions are real-valued, nonnegative, fair, and normalized to one at
the empty transcript. Their computability is witnessed by a single computable
function giving rational approximations to error at most `2^-n`, uniformly in
the finite transcript and precision. Rational outputs are encoded by their
canonical numerator and denominator. This avoids silently restricting capital
functions to exact rational values.

Success is **unboundedness** of capital, not convergence of capital to infinity.
The distinction matters in the normalization argument. Ordinary increasing
scans are included, and KL randomness implies computable randomness for these
definitions.

The standard implication **ML randomness ⇒ KL randomness** is now proved for
these exact definitions. `MaximalInequality` gives

\[
\lambda\{X:\exists n,\ d(\operatorname{transcript}_\pi(X,n))>2^m\}\le 2^{-m}
\]

by a finite hitting-tree induction and a monotone limit. `EffectiveScan`
turns a computable condition on finite adaptive transcripts into a uniformly
c.e. union of input cylinders. For a rational approximation `q(v,0)` with
error at most one, the test enumerates transcripts satisfying
`q(v,0)>2^m+1`. Every such input crosses the capital threshold `2^m`, and
unbounded capital eventually exceeds `2^m+2`, forcing membership in every
test level. Thus even a fixed approximation precision suffices for this
particular test. `MLImpliesKL` constructs the genuine `MartinLofTest` and
proves the implication.

The finite transcript law is proved directly. For a fixed transcript `v`, its
queries form a fixed injective list of coordinates, even though the rule is
adaptive. Its input event is the corresponding finite assignment cylinder, so

\[
\lambda\{X:\operatorname{transcript}_{\pi}(X,|v|)=v\}=2^{-|v|}.
\]

### Total and partial strategies

The paper explicitly uses total strategies. Its cited source supports this:
Miller and Nies, *Randomness and computability: open questions*, discussion
following Definition 6.1, printed page 10, states that a partial test can be
replaced by two total, even primitive recursive, tests whose success sets cover
its success set.

The construction is now implemented for partial rational-wager programs. Each
of two simulators bets only on one parity of input positions and reads fresh
positions of the other parity while waiting for a computation. Answers read
while waiting are cached and replayed if the source later requests them. This
is necessary to retain the no-repeated-query condition.

The code proves primitive recursive fresh-query scheduling, liveness on an
infinite source run, nonnegative fair capital, and exact simulation of the
selected parity factor. The product of the two source factors is the original
capital, so an unbounded source forces at least one factor to be unbounded.
The [Miller–Nies note](miller-nies.md) records the checked statement and the
precise scope of the program model. Conversion of arbitrary partial
computable-real capital to rational wagers remains a distinct effectivity
obligation; no general real-capital equivalence is assumed.

Primary source: [Miller–Nies paper](https://people.math.wisc.edu/~jsmiller8/Papers/questionsfinal.pdf).
The parity simulation is described in
[Bienvenu's thesis](https://www.labri.fr/perso/lbienvenu/docs/publications/bienvenu-phd.pdf),
Remark 1.7.7, printed page 35, attributed there to Merkle.

## Review of the paper's central arguments

### 1. Affine constraints and forced answers — Section 3, pages 3–4

Let `D` be the matrix of unread columns other than the next queried column `c`.
For residual syndrome `z`, the two possible answers have completion sets

\[
D x=z,\qquad D x=z-c.
\]

If `c` lies in the range of `D`, subtracting a preimage of `c` gives a bijection
between the two fibers. They therefore have equal cardinalities. If `c` is
outside that range, both fibers cannot be nonempty: subtracting two solutions
would put `c` in the range. Provided the history is compatible, exactly one bit
is then possible.

`Klr/Affine.lean` proves these facts, the equivalence with a rank drop, and that
the rank drop is exactly one. It also proves the solution count `2^(m-r)` for
a surjective binary linear map from `m` bits to `r` equations and the fraction
`2^-r` of assignments satisfying the equations.

The full-unread-rank observation law is now proved. For a finite family of old
constraints `A`, a disjoint new block `E` of rank `r`, and an adaptive transcript
`v` leaving full unread rank, the actual conditioned measure satisfies

\[
\lambda(C_\pi(v)\cap E\mid A)
  =2^{-r}\lambda(C_\pi(v)\mid A).
\]

The proof constructs the finite ambient coordinates and counts residual
syndrome fibers. It does not assume the desired independence. Null transcript
events are included. Pairwise disjoint old blocks are proved to have positive
joint probability, and normalizing by the new syndrome's mass gives equality
of old/new stage transcript probabilities. See the
[finite-stage note](finite-stage.md) for the precise module interfaces.

`AffineAnswer` now proves the conditional fair-or-forced answer law after
**arbitrary partial rank loss**. On a positive-probability history satisfying
the old equations, the new equations, and the transcript, a next query inside
the new block is fair exactly when the remaining rank does not drop. If it
drops, every compatible input has the same next bit, whose conditional
probability is one. A query outside all conditioned blocks is fair.
The proof constructs a kernel translation preserving both the history and
the concrete fair-coin measure while swapping answer events in the fair case.
Compatibility remains explicit: an impossible history has no conditional
bit distribution of the intended kind.

### 2. Square-summable normalization — Lemma 2, pages 4–5

After the positive-reserve and rational approximation step, the capital is
bounded below by `1/4`. With original signed wager fractions `f_t`, put

\[
Q_n=\sum_{t<n}f_t^2,
\qquad
h_t=\frac{f_t}{2(1+Q_t)}.
\]

The elementary telescoping bound is now formalized:

\[
\sum_{t<n}h_t^2
\le \frac12\left(1-\frac1{1+Q_n}\right)
\le\frac12,
\qquad
\sum_{t=0}^{\infty}h_t^2\le\frac12.
\]

The reserve is essential to the informal success-preservation argument. If
`M_n` is the sum of the signed original returns, then the paper obtains

\[
M_n\ge -\log4+Q_n/4.
\]

Abel summation against the positive decreasing factors `1/(2(1+Q_t))` then
handles bounded and unbounded `Q_n` separately. When `Q_n` is bounded, the
factors stay away from zero. When it is unbounded, the lower bound supplies
logarithmic growth of the damped cumulative returns. The new analytic module
uses a sufficient `1/6` coefficient in the corresponding log estimate where
convenient; this is a proof simplification, not a correction to the paper's
stronger `1/4` inequality.

The full deterministic implication is now proved as
`normalization_preserves_unbounded_capital`. If

\[
C_n=\prod_{t<n}(1+x_t)\ge\delta>0,
\qquad |x_t|<1,
\]

and `C_n` is unbounded, then

\[
D_n=\prod_{t<n}\left(1+\frac{x_t}{2(1+\sum_{s<t}x_s^2)}\right)
\]

is unbounded. Here `x_t` is the signed return along a fixed transcript, so
`x_t²=f_t²` and this is the same damping as in the paper.

The full effective strategy lemma is now proved in
`EffectiveNormalization` and `EffectiveNormalizationStrategy`. The first
module approximates the **additive stake** of `(d+1)/2` at a transcript `v`
by

\[
\widetilde s(v)
=\frac{q(v1,|v|+2)-q(v0,|v|+2)}4.
\]

It accumulates these signed rational stakes into a fair rational capital
`r(v)`. The geometric error budget gives the uniform all-branch estimate

\[
\left|r(v)-\frac{d(v)+1}{2}\right|
\le\frac14(1-2^{-|v|})\le\frac14.
\]

Consequently `r(v)≥1/4`, its wager fractions have absolute value strictly
less than one, and success of `d` implies success of `r`. Approximating
stakes this way preserves fairness exactly and controls accumulated error
without a lower bound on the original capital.

The second module applies the proved damping argument to this rational
reserve process, explicitly proves computability of the rational folds and
arithmetic, and constructs `s.normalize : BettingStrategy`. The scan is
unchanged. On every input the normalized wagers have absolute value at most
`1/2` and squared sum at most `1/2`; normalized capital stays positive; and
`s.Succeeds X → s.normalize.Succeeds X` is proved. Selecting the approximation
witness uses classical choice, but its computability is part of the original
strategy and is proved for the resulting capital. No effective enumeration
of all total strategies is assumed.

### 3. Computable pools — Lemma 3, pages 6–8

The weak-limit construction produces Borel sets `H_i`, `L_i` shared across
stages. These sets and the weakly convergent subsequence need not be computable.
For each fixed stage, finite clopen/simple-function approximations are chosen
and hard-coded into the pool program.

The third search condition, involving the weighted average of query
probabilities, is crucial. It bounds how much additional querying can occur
after the search horizon. The finite-time approximation condition alone would
not control the limiting unread fraction.

The reviewed constants give the claimed error bounds. A diagonal weak limit,
finite approximations, and a limsup bound on the weighted query probability
together justify termination for every sufficiently large pool size. The pool
program is not claimed to halt at every smaller size.

**Formal status:** this lemma is not yet encoded. It needs a careful combination
of weak convergence in `L²`, Borel representatives, approximation by cylinder
functions, and an explicit finite search. The finite advice must be fixed before
the trial pool size is supplied.

### 4. Sparse rank-preserving lists — Lemma 4, pages 8–9

The list size `J=M^3` makes the failure probability small enough to union-bound
over all `2^M` unread subsets as well as all pool positions. The conditioning
on full row rank costs at most the stated factor of two for sufficiently large
rank. No conflicting dependence on the unread set was found in the review.

`Klr/Sparse.lean` proves the deterministic estimate used after such a list has
been constructed. If a position appears in at most a fraction `δ` of the
candidates, and the pool's nonnegative weights satisfy `∑ w_a² ≤ C`, then

\[
\frac1J\sum_q\sum_{a\in S_q}w_a
\le \delta\sqrt{M C}.
\]

This is double counting followed by Cauchy–Schwarz; it also yields a candidate
no worse than the average. With the paper's parameters, it explains the
decaying average total wager. It does **not** prove existence of a list having
both sparsity and rank preservation. That probabilistic-method argument remains.

### 5. Short descriptions and advice — Section 5, pages 9–12

There is no computable enumeration of all total computable strategies of the
kind one might accidentally assume while encoding the construction. The paper
does not require one: its list is non-effective, and a stage only uses finitely
many actual program codes.

`StrategyCountability` proves countability of the actual `BettingStrategy`
type, including real-valued capital. It chooses program codes for the scan
and one uniform rational approximating function. Equality of approximation
functions implies equality of real capitals by the vanishing error bound.
The resulting injection into a countable space of code data justifies the
almost-everywhere interchange of quantifiers over **all** total strategies.
It makes no claim that totality can be decided or effectively enumerated.

For fixed stage `j`, the header includes the earlier constraints, relevant
strategy programs, the pool program, and fixed stage parameters. Its size may
be enormous and noncomputably dependent on `j`, but is independent of the trial
rank `r`.

Two non-effective choices have short encodings:

- The chosen candidate index is smaller than `J=r^24`, so costs `O(log r)` bits.
- The horizon advice integer `b_j` is bounded by `j/e_j`, independently of `r`.

The syndrome is computed by finite minimization once this data is supplied.
Writing the syndrome literally would cost `r` bits and break the argument;
reconstructing it is therefore a central part of the proof.

The description budget in Section 3 uses **plain**, not prefix-free, programs.
There are `2^d` descriptions of length `d`, and

\[
\sum_{p\in2^{<\omega}}2^{-2|p|-n-1}=2^{-n}.
\]

The budget module formalizes this counting and summation step, the resulting
measure bound, and a genuine ML test obtained from any uniformly c.e. family of
cylinder unions satisfying those per-description bounds. Its uniformity proof
uses a formal dovetailing search for existential quantification over c.e.
predicates. Supplying the actual affine-system decoder, proving its
effectiveness, and deriving the stage-specific program-length bound are
separate remaining obligations. A big-O annotation on a theorem statement
would not discharge them.

### 6. The final measure — Section 6, pages 12–14

Simply transferring a small-probability event from a finite-stage law to the
final measure could introduce an uncontrolled conditioning factor. The paper
avoids this by comparing transcript cylinders immediately before the first
relevant rank drop. At that point, later blocks still have full remaining rank,
so their syndromes do not change the probability of the cylinder.

Equality on the event of *no first drop ever* is obtained by decreasing limits
of finite-horizon events and then uniqueness on the cylinder-generated Borel
σ-algebra. The sets `H_i`, `L_i` must be interpreted consistently in transcript
space when these equalities are used.

The subsequent late-drop bounds are summable. Borel–Cantelli controls all but
finitely many late blocks, while the early total wagers have finite expectation.
The paper then uses square-summable increments and an `L²` martingale
convergence theorem to bound capital. The formalization uses the simpler
product argument described below for this final step.

**Formal status:** finite-stage cylinder preservation and the first-rank-drop
tail transfer are proved. The latter uses a prefix-free countable family of
pre-drop transcripts and has no finite upper bound on the stopping time. The
numerical remaining rank is proved nonincreasing, and the stopping event is
proved equivalent to the first strict numerical rank decrease.

`NoDrop.nextStage_map_restrict_noDrop` now proves equation (10): equality
of old/new transcript laws restricted to no rank drop ever. The proof passes
from finite-horizon cylinder partitions to a decreasing intersection, then
uses uniqueness on the cylinder-generated measurable structure. It handles
all Borel transcript events and requires no positive mass of the no-drop
event. The conditional fair-or-forced answer law is also proved, as described
above.

`PrefixStage` and `BlockProduct` now construct the actual infinite block
measure. For every finite set of coordinates, the marginal is the stage law
after all blocks meeting those coordinates have been imposed. Disjointness
of supports proves that the marginal stabilizes, and the stabilized marginals
are proved consistent. Mathlib's Kolmogorov extension theorem supplies the
probability measure with exactly those marginals. The intersection of all
block equations has measure one.

The resulting cylinder comparison with a finite stage is proved under full
unread rank of every later block. `FutureNoDrop` extends it to Borel transcript
restrictions and the first subsequent rank-drop event for all blocks beyond
a specified index. Its safety cutoff and comparison-stage cutoff are separate,
so it directly handles the paper's event tracking the current block together
with all later ones while comparing to the stage already imposing that block.
`BlockProductAnswer` also transports the conditional fair-or-forced answer
law to the actual infinite measure. Its child-cylinder mass statements include
zero-mass histories.

#### A simpler final boundedness argument

`FairForced` factors normalized capital as

\[
D_n=F_nG_n,
\]

where `F_n` multiplies the usual return factor only at fair queries and `G_n`
only at forced queries. Both products are nonnegative. The actual fair
child-cylinder identity proves conservation of capital-weighted probability
mass for `F`. A finite-tree maximal inequality and a limit therefore show that
`F_n` is bounded almost surely. For the other factor,

\[
G_n\le\exp\!\left(\sum_{t<n,\ \text{forced}}|h_t|\right).
\]

Thus summability of the absolute forced wagers implies boundedness of `D_n`
almost surely. This avoids a separate formalization of the `L²` martingale
argument. It is an alternative proof of the same conclusion, not a correction
to the paper. Square summability of normalized wagers is still needed upstream
for the candidate-support wager estimate.

`BlockRandomness` connects this result to the actual infinite block measure,
success-preserving normalization, and countability of strategies. It proves
almost-sure KL randomness from almost-sure forced-wager summability for each
normalized strategy. It then proves conditional existence of a separating
sequence if the common block solutions are covered by one genuine Martin-Löf
test. A second interface derives that test from `DescriptionBudget`'s uniform
c.e. description family and explicit per-description bounds.

These are conditional reductions. They do not construct a block sequence
satisfying the required wager estimates and short-description properties.

#### From the finite-stage estimates to equation (11)

That intermediate implication is also now proved. `StageEstimates` records
the combined early-wager/partial-rank estimate (6), the first-drop bound (7),
the `H`/no-drop estimate (8), the particular earlier-law instances of (9)
needed for the later-block union bound, and all-branch horizon avoidance.
These properties are only required beyond a strategy-dependent finite block
index. Its Borel set `H` is fixed across those stages.

`HorizonAvoidance` constructs the finite set of all queries made on all
branches through a horizon. `HorizonLaw` transports finite-answer distributions
and the actual early-wager expectation from the finite stage to `ρ`.
`LateDropBound` proves the event decomposition giving

\[
\rho(\text{late drop in block }j)
\le 7e_j+\sum_{k>j}e_k=8e_j.
\]

`StageErrorBudget` proves the exact dyadic tail identity and the summability
of these bounds. `EarlyLateWagers` proves equation (11) from the two actual
early/late estimates using Borel–Cantelli, finite expected early total, and
freshness on each finite block. Finite initial exceptions are handled
pathwise, without additional estimates.

Consequently `ae_kolmogorovLovelandRandom_of_stage_estimates` proves
almost-sure KL randomness under the actual constructed law, and
`exists_separating_of_stage_estimates_and_descriptions` gives the separating
sequence when the effective description contract is also supplied.
The [stage-estimates note](stage-estimates.md) states all hypotheses, including
the zero-based stage convention. The remaining task is their simultaneous
construction; the code does not posit those witnesses as axioms.

## Suggested dependency order

1. Prove the probabilistic construction of sparse rank-preserving lists, using
   the existing incidence/weight estimate downstream.
2. Formalize the computable pool lemma, preserving the order of its
   non-effective finite choices and its effective search.
3. Construct the effective affine decoder and rank filter used by the
   description-budget test.
4. Encode the stage construction and its actual descriptions, including the
   reconstruction of horizons and syndromes, proving the `StageEstimates`
   and description-cover contracts simultaneously.
5. Apply the checked final reduction to those constructed witnesses and
   audit the resulting unconditional theorem's axioms.

The effective normalization, infinite block law, no-drop and conditional
answer identities, quantitative Section 6 reduction, and `MLR → KLR` check
now provide the required downstream interfaces. A full partial-real source-model bridge can be
treated separately; the paper's construction uses total strategies.

## Dependencies

Mathlib is the only direct library dependency. The project uses Mathlib's
`REPred`, program codes, finite linear algebra, and probability library, with
the additional rational arithmetic and strategy infrastructure developed here.

## References

- [Liu–Meng, arXiv:2611.31004v1](https://arxiv.org/abs/2611.31004v1).
- [Miller–Nies, *Randomness and computability: open questions*](https://people.math.wisc.edu/~jsmiller8/Papers/questionsfinal.pdf), especially Section 6.
- [Bienvenu, doctoral thesis](https://www.labri.fr/perso/lbienvenu/docs/publications/bienvenu-phd.pdf), Remark 1.7.7.
- [Mathlib v4.36.0](https://github.com/leanprover-community/mathlib4/tree/v4.36.0).
