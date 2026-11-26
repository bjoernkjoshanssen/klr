# Sparse rank-preserving candidate lists

Lemma 4's combinatorial existence and effective construction are now proved
in Lean. The mathematical existence theorem is

```lean
Klr.SparseCandidateList.eventually_exists_goodList
```

The actual partial-recursive construction and its eventual correctness are

```lean
Klr.SparseListConstruction.partrec_construct
Klr.SparseListConstruction.eventually_construct_good
```

These lists are now used in the completed simultaneous stage construction.
[`StageConstruction`](../Klr/StageConstruction.lean) combines them with the
fixed pool programs, actual wager estimates, horizon search, and computed
syndromes. [`Separation`](../Klr/Separation.lean) proves the unconditional
separation theorem for the repository's **total computable-real
betting-strategy convention**. A general partial computable-real convention
requires a separate bridge; see the
[stage-construction note](stage-construction.md) for the exact scope and
assembly.

For every fixed positive real density `τ` and error tolerance `θ`, it proves
that every sufficiently large natural `r` admits a list of

$$
J=M^3,\qquad M=r^8,\qquad m=r^2
$$

candidates. Each candidate has a support of exactly `m` positions in
`Fin M` and an actual full-row-rank binary matrix with `r` rows and `m`
columns. Repetitions in the list are allowed, as in the paper's independent
sampling argument.

The list satisfies both requirements simultaneously:

$$
\#\{q<J:a\in S_q\}\le\frac{2m}{M}J
\quad(a<M),
$$

and

$$
\#\{q<J:\operatorname{rank}(B_q|_{S_q\cap D})<r\}
\le\theta J
\quad\text{whenever }|D|\ge\tau M.
$$

The theorem does not assume the probability estimates or an asymptotic
smallness condition: they are proved from finite counting and the displayed
polynomial parameter choices. `exists_goodList_above` supplies a rank and a
list above any prescribed lower bound. The result applies in particular to
the paper's positive rational parameters below one.

## The actual finite experiment

`FiniteProbability` defines uniform probability on a finite type by normalized
counting and expectation by a normalized finite sum. Independence of the
samples is the proved factorization of product sums. There is no unspecified
probability distribution in the candidate argument.

`UniformSupportCount` and `UniformSupport` use

```lean
{S : Finset (Fin M) // S.card = m}
```

as the uniform support sample space. Exact binomial counts establish

$$
\Pr(a\in S)=\frac mM,\qquad
\Pr(a,b\in S)=\frac{m(m-1)}{M(M-1)}\quad(a\ne b).
$$

For `N = |S ∩ D|`, the resulting first and second moments give

$$
\mu=\mathbb E N=\frac{m|D|}{M},\qquad
\operatorname{Var}(N)\le\mu.
$$

Consequently, when `|D| ≥ τ M` and `4r ≤ τ m`,

$$
\Pr(N<2r)\le\frac4{\tau m}.
$$

The code's elementary size assumptions are `2 ≤ m ≤ M`. They hold in the
eventual polynomial regime.

## Uniform matrices and conditioning

`RandomMatrixAlgebra` characterizes failure of full row rank by a nonzero
linear functional annihilating all selected columns. For each such functional,
the evaluations on any selected column set `T` are uniformly distributed in
`(ZMod 2)^T`. `RandomMatrix` therefore proves the exact annihilation probability
`2^(-|T|)` and the union bound

$$
\Pr(B|_T\text{ loses full row rank})
\le(2^r-1)2^{-|T|}.
$$

The full-rank matrices form an actual finite subtype. The proof identifies
uniform probability on that subtype with ordinary conditional counting
probability. If `r+1 ≤ m`, the full-rank event has probability at least one
half. Thus conditioning increases a failure probability by at most a factor
of two; for `|T| ≥ 2r`, the conditional failure probability is at most

$$
2\cdot2^{-r}.
$$

`SparseCandidate` combines the support and full-rank matrix experiments as
an independent product. A fixed enumeration of each support identifies
matrix columns with pool positions. It proves that the number of selected
columns is exactly `|S ∩ D|`, and obtains the actual marginal bounds

$$
\Pr(a\in S)=\frac mM,\qquad
\Pr(\operatorname{BadRank}(D))
\le\frac4{\tau m}+2\cdot2^{-r}.
$$

## Concentration and all unread sets at once

`SampleConcentration` proves the exact generating-function identity

$$
\mathbb E\,b^{\#\{q:z_q\in A\}}
=\bigl(1+(b-1)\Pr(A)\bigr)^J.
$$

Finite Markov bounds then yield the following sufficient estimates:

$$
\Pr\bigl(\#\{q:z_q\in A\}>\theta J\bigr)
\le e^{-\theta J/4}
\quad\text{if }\Pr(A)\le\theta/4,
$$

$$
\Pr\bigl(\#\{q:z_q\in A\}>2pJ\bigr)
\le e^{-pJ/6}
\quad\text{if }\Pr(A)\le p.
$$

The first uses base `2` and `log 2 ≥ 1/2`; the second uses base `3/2` and
`log(3/2) ≥ 1/3`. These exponents are weaker than the paper's but sufficient
for its parameter choices. This is a simplification of the formal proof,
not a correction of the paper's concentration argument.

The union runs over all `2^M` unread sets and all `M` pool positions. Using
`2^M ≤ exp M`, its failure probability is at most

$$
e^{M-\theta J/4}+M e^{-mJ/(6M)}.
$$

`SparseParameters` proves that the single-candidate bound is eventually at
most `θ/4` and that this total list-failure bound tends to zero. With
`J=M^3`, the second exponential becomes `exp(-m M²/6)`. Eventually both
negative exponents dominate `-M`, so the total is bounded by
`exp(-M) + M exp(-M)`, which tends to zero. A finite experiment with failure
probability less than one has a successful outcome, giving the list.

## Connection to support weights

`SparseCandidateWeights` connects the list's incidence statement directly
to the previously proved deterministic `Sparse` API. If `w(a) ≥ 0` and
`∑ a, w(a)^2 ≤ C`, then

$$
\frac1J\sum_{q<J}\sum_{a\in S_q}w(a)
\le\frac{2m}{M}\sqrt{MC}.
$$

If `J>0` and `θ<1`, the rank-preserving indices for any dense `D` number
at least `(1-θ)J`. Restricting the average to those indices gives a candidate
which both preserves rank on `D` and satisfies

$$
\sum_{a\in S_q}w(a)
\le\frac{2m/M}{1-\theta}\sqrt{MC}.
$$

The direct wrapper is `exists_rank_good_small_weight_of_isGood`. This is a
useful deterministic API for one prescribed dense set. The stage
construction uses the complete-list average: its unread sets depend on the
answer sequence, and one candidate must control both actual wager
expectations and the integrated low-set rank-drop probability.

`SparseListWeights` supplies the same bounds directly for a verified code
list. Its `exists_rank_good_small_weight_of_construct` takes an actual
successful output of `construct` and returns an entry of that list whose
masked matrix keeps full rank and whose support has the displayed weight
bound. No reverse decoding to the probabilistic candidate type is required.

### Actual normalized wagers and simultaneous candidate selection

[`StageWeights`](../Klr/StageWeights.lean) defines the all-time absolute wager
at a position, then sums it over a finite support. Freshness ensures that a
position contributes at most once on each input. The normalized pathwise
square-sum bound and Cauchy–Schwarz give

$$
\sum_{a\in G} w_i(a,X)\le\sqrt{M/2}.
$$

Applying the list's incidence bound before integrating under the actual
old-stage law $P_n$ gives, for each protected strategy,

$$
\frac1J\sum_{q<J}\mathbb E_{P_n}
  \sum_{a\in S_q}w_i(a,X)
\le\frac{2m}{M}\sqrt{M/2}
=\frac{\sqrt2}{r^2}.
$$

This estimate holds for an arbitrary probability law. The supports in the
formula are the actual natural-number positions obtained by embedding the
candidate masks in the concrete pool list.

[`StageRank`](../Klr/StageRank.lean) identifies the candidate's restricted
matrix on a finite unread mask with the actual unread affine map. Passing
to the eventual unread pool gives the all-time no-drop correspondence.
[`StageRankAverage`](../Klr/StageRankAverage.lean) integrates the list's bad
rank count. If the pool's low-set failure probability is at most $\eta$,
the resulting average low-set drop probability is at most $\eta+\theta$.

[`StageChoice`](../Klr/StageChoice.lean) selects one index from the sum of
these two scores over all protected strategies. The rank score is multiplied
by the old-law density bound $2^K$, where $K$ is the sum of preceding block
ranks. For $\ell$ protected scans, the complete-list average is at most

$$
\ell\left(\frac{\sqrt2}{r^2}+2^K(\eta+\theta)\right).
$$

The tolerances are chosen before $r$, and the first term tends to zero.
Consequently one actual list position simultaneously satisfies the
support-wager and low-drop budgets. The conclusions hold for every later
syndrome, since these scores depend only on the support and unread ranks.
This is the candidate used by `StagePreHorizon` and `StagePrepared`.

## The effective exhaustive search

The existence theorem is classical, as is the probabilistic argument in the
paper. It uses a chosen enumeration of each finite support and does not claim
that this choice is a computable enumeration.

`SparseListSearch` instead uses ordinary finite data: a list of pairs of a
Boolean support mask and an `AffineCode.Data` matrix code. The matrix has
ambient width `M`, has `r` rows, and is zero off its mask. The verifier checks
the mask has exactly `m` true bits and that the matrix has full row rank.
`GoodEntry.restricted_fullRank` and `GoodEntry.selectedColumns_card` explicitly
prove that deleting the padded columns gives a full-row-rank matrix on
exactly `m` columns.

The finite list checker verifies every coordinate incidence and every
length-`M` Boolean unread mask. Incidence is expressed without division as
`M * count ≤ 2*m*J`; density and rank-failure comparisons use exact rational
arithmetic. It preserves multiplicities, so repeated candidates count as
different list positions.

`SparseSearchRank` explicitly enumerates Boolean vectors and checks matrix
surjectivity. `SparseSearchMask` zeros the excluded columns and proves that
its executable rank result agrees with the actual restricted linear map.
`SparseListSearchComputable` proves computability of the entire finite list
checker, including the dynamic loops and rational comparisons.

`SparseListSearchEffective.search` enumerates ordinary natural encodings of
finite lists and returns the first accepted list. It is proved partial
recursive; its domain is exactly the set of parameter tuples admitting a
good code, and every returned list satisfies the full specification. The
module also extracts a single actual Mathlib program using the explicit
canonical encoding of its rational-containing parameter tuple.

`SparseCandidateCode` pads a mathematical candidate's matrix and proves that
padding preserves every restriction-rank predicate. `SparseCodeCount` and
`SparseListCodeBridge` preserve the support cardinalities, incidence counts,
and bad-rank counts exactly. Thus every mathematical witness yields a code
accepted by the finite checker. This encoding is used only to establish
existence; the exhaustive search does not attempt to compute the chosen
support enumerations.

Finally,

```lean
SparseListConstruction.construct (τ θ : ℚ) (r : ℕ)
```

specializes the actual search to `M=r^8`, `m=r^2`, and `J=M^3`. It is partial
recursive for fixed `τ, θ`, is correct whenever it returns, and halts for
every sufficiently large `r` when both rational parameters are positive.
There is also a theorem extracting an actual partial-recursive program for
this fixed-parameter construction. This proves the effective conclusion of
Lemma 4 without an assumed computable witness selector.

The sparse-list output itself leaves the stage syndrome to the later finite
minimization. Its certificate field is also unrestricted, since the direct
rank verifier does not need a certificate. `SparseSearchCertificate` can
compute a right inverse for any such full-row-rank matrix, preserving a
supplied syndrome and the corresponding affine event.

In the completed stage, `StageSyndromeObjective` computes the minimizing
syndrome from exact rational expectations. `StageCandidateCode` then
reconstructs a verified code with the selected event and rank. The entire
procedure is part of one actual `StageReconstruction` program, which
reproduces the same [computable pool](computable-pools.md) and sparse list.
Only the rank $r$, list index $q<r^{24}$, and bounded integer horizon advice
vary in its input. The
[affine-description note](affine-descriptions.md) explains the resulting
short-program bound, and the
[stage-construction note](stage-construction.md) explains how the stages
are assembled into the final sequence.
