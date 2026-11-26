# Finite-stage identities, conditional answers, and no-drop events

This note records the probability identities used in Sections 3 and 5 of
[Liu–Meng, version 1](https://arxiv.org/abs/2611.31004v1), including the
zero-probability case, the countable stopping-event step, and equality on Borel
transcript events when no rank drop ever occurs. All measures in
the statements below are constructed from the repository's fair-coin measure.

## The block theorem

An `AffineBlock` consists of a finite support `S ⊆ ℕ`, a number of rows `r`, a
surjective linear map

\[
B:\mathbb F_2^S\longrightarrow\mathbb F_2^r,
\]

and a syndrome `y`. Its event is

\[
E=\{X:B(X\mathbin{\upharpoonright}S)=y\}.
\]

Surjectivity is the formal statement of full row rank. For a fixed transcript
`v` of a scan rule `π`, let `Qπ(v)` be its finite set of queried positions. The
predicate `UnreadFullRank B π v` says that the map using only the columns in
`S \ Qπ(v)` is still surjective.

For a finite family of earlier blocks, put

\[
A=\bigcap_{k<j}E_k,\qquad P_{j-1}=\lambda(\,\cdot\mid A).
\]

`AffineBlock.finiteStage_identity` proves

\[
P_{j-1}(C_\pi(v)\cap E)
  =2^{-r}P_{j-1}(C_\pi(v))
\]

from disjointness of `S` from every earlier support and full unread rank after
`v`. There is no assumed independence theorem in the hypotheses. The proof
constructs the necessary finite coordinate model itself.

The more general `finiteStage_identity_of_dependsOn` allows any earlier event
depending on a finite support disjoint from `S`. Earlier constraints need not
be independent of one another for the intersection identity. If their
conjunction is null, Mathlib's conditional measure is zero and the identity
still holds.

## Why the probability factor is exact

The proof has three separate ingredients.

1. **Uniform finite-coordinate law.** `FiniteMeasure` proves that an injective
   selection of `m` input coordinates has the uniform distribution on
   `𝔽₂^m`. A set of assignments therefore has probability equal to its
   cardinality times `2^-m`.
2. **Residual affine fibers.** `AffineObservation` splits a finite assignment
   into its observed and unread parts. For each observed value `o`, the new
   equation becomes

   \[
   B_U u=y-B_Oo.
   \]

   If `B_U` is onto, this fiber has exactly `2^(|U|-r)` elements. This number
   is independent of `o` and of the residual syndrome. Summing over any
   predicate `P(o)` gives the natural-number identity

   \[
   |\{x:P(x_O)\land Bx=y\}|\,2^r=|\{x:P(x_O)\}|.
   \]

3. **Actual conditioning.** `FiniteStage` transports that count to the
   fair-coin measure and uses Mathlib's definition

   \[
   \lambda(\,\cdot\mid A)=\lambda(A)^{-1}\lambda\mathbin{\upharpoonright}A.
   \]

   The normalization is by `λ(A)`, never by the probability of the particular
   transcript. This is why the formula covers null transcript events without
   a positive-probability proviso.

To apply these ingredients, `AffineBlock` takes the union of the old supports,
the new support, and the transcript's queried positions as its ambient set.
It declares all old coordinates and all queried coordinates observed. The
remaining variables are exactly the relevant unread new-block coordinates;
the old event and the fixed transcript become predicates on the observed
values. The adaptive choice of queries causes no additional independence
assumption: after `v` is fixed, all query positions along `v` are fixed.

## Positive stage measures and normalization

`AffineFamily` proves, for pairwise disjoint full-rank blocks,

\[
\lambda\Bigl(\bigcap_{k<j}E_k\Bigr)
 =\prod_{k<j}2^{-r_k}>0.
\]

Thus the finite-stage laws are probability measures. A disjoint new block has
probability `2^-r` under the old stage law, and division by this nonzero value
gives the normalized cylinder identity

\[
\lambda(C_\pi(v)\mid A\cap E)=\lambda(C_\pi(v)\mid A)
\]

whenever its unread columns remain full rank. The theorem is named
`AffineBlock.nextStageLaw_transcript`.

## From cylinders to the first-drop tail

`StoppingTranscript` formalizes input events for finite transcripts and proves
that a prefix-free family of transcripts gives pairwise disjoint input events.
It then proves exact countable-sum formulas and transfers both probability
equalities and constant probability factors through those sums.

For a predicate `B(v)` known before the next query, `firstTrigger B` consists of
the transcripts where `B` first holds. It is prefix-free. The tail version
keeps transcripts with `|v| ≥ N`. Its input event is characterized directly as
the existence of a first triggering time at or after `N`.

For an affine block, the trigger is

\[
\operatorname{Full}(v)\ \land\
\neg\operatorname{Full}(v0).
\]

Appending `0` or `1` gives the same queried-position set: the next position is
selected before the new bit is observed. Hence this is a predictable loss of
full unread rank, not a condition selected using the next answer.

Every pre-trigger transcript still has full unread rank, so the finite-stage
identity applies to every summand. Consequently the old and new stage laws
assign the same probability to the first-drop tail. There is no finite upper
bound on the stopping time in this theorem. With the paper's one-based query
index, a pre-drop transcript of length at least `N` corresponds to
`N < T < ∞`.

`RemainingRank` closes the connection with the paper's numerical rank
definition. It defines the rank as the dimension of the unread map's image,
proves that it starts at `r` and never increases, and proves that full unread
rank is equivalent to numerical rank `r`. It then identifies the event above
with

\[
\exists t>N\;\bigl[R(t)<R(t-1)\ \land\
  \forall\,0<s<t,\ R(s)\not<R(s-1)\bigr].
\]

`StoppingTranscript.nextStage_strictRankDropTail` proves preservation of this
numerically defined first-drop tail under the new syndrome conditioning.

## Conditional answers after partial rank loss

The cylinder identity above requires full unread rank. The next-answer law
does not. `AffineAnswer` conditions on the actual history

\[
H=(A\cap E)\cap C_\pi(v),\qquad \lambda(H)>0.
\]

Let `a = π(v)` be the next queried coordinate in the new block. The module
proves the following equivalence for the current remaining rank, even when
earlier observations have already lowered it:

\[
\bigl[\forall b\in\{0,1\},\ \lambda(X(a)=b\mid H)=1/2\bigr]
\quad\Longleftrightarrow\quad
R(vb)=R(v).
\]

The value `R(vb)` is independent of `b`, since the next coordinate is selected
before its answer is known. If the rank strictly decreases, there is instead
a bit `b` such that **every** input in `H` has `X(a)=b`; its conditional
probability is one and the other bit's is zero. A fresh coordinate outside
all constrained blocks has conditional probabilities one half each.

The probability argument is concrete. The algebraic column-span condition
provides a kernel vector vanishing at all observed coordinates and equal to
one at `a`. Adding that vector in `𝔽₂` preserves the old constraints, the new
constraint, the transcript, and fair-coin measure, while swapping the two
answer events. `AffineAnswerMeasure` proves the required measure-preserving
translation of the infinite product directly.

`AffineAnswer.cond_stage_transcript` identifies conditioning on `H` with
conditioning the current stage law on `Cπ(v)`. The public theorem
`stage_next_answer_fair_iff_no_rank_drop` therefore applies to the actual
stage law. Positive history mass is essential here: this is a probability
distribution given an observed history, unlike the unnormalized intersection
identity for which null histories were harmless.

## Equality of Borel transcript laws on no drop

Let `T` be the first strict remaining-rank decrease for the new block, with
`T=∞` if there is none. `NoDrop` defines the actual observation map

\[
O_\pi(X)(n)=X\bigl(\pi(\operatorname{transcript}_\pi(X,n))\bigr)
\]

and proves its measurability. It also proves that input cylinders generate
the measurable structure of Cantor space and determine finite measures.

For a fixed transcript cylinder and a finite horizon, the event that rank
stays full through that horizon is a disjoint union of equal-length transcript
events. The stage identity applies to each member. Taking the decreasing
intersection of these finite-horizon events gives equality on that cylinder
intersected with `{T=∞}`. Uniqueness of finite measures then extends equality
to **every Borel set of transcripts**.

Writing `N` for the transcript-space no-drop event, the strongest statement is

\[
(O_{\pi*}P_j)\mathbin{\upharpoonright}N
=
(O_{\pi*}P_{j-1})\mathbin{\upharpoonright}N.
\]

This is `NoDrop.nextStage_map_restrict_noDrop`, the finite-stage identity in
equation (10) of the paper. Equivalently, `nextStage_noDrop_borel` states

\[
P_j(O_\pi^{-1}(F)\cap\{T=\infty\})
=P_{j-1}(O_\pi^{-1}(F)\cap\{T=\infty\})
\]

for every measurable transcript set `F`. These are restrictions, not
renormalized conditional measures; no positive probability of `{T=∞}` is
needed. This distinction allows later use of arbitrary Borel sets such as
the pool lemma's `H_i` and `L_i` in transcript space.

## The infinite block law

For a sequence of pairwise disjoint blocks, `PrefixStage.law B n` conditions
on exactly the blocks with indices `k<n`. This zero-based convention differs
from the paper's one-based labels: the stage imposing block `j` is `j+1` in
this API.

A finite coordinate set meets only finitely many blocks, because each of
its coordinates belongs to at most one block. `BlockProduct.cutoff` bounds
their indices. The finite-coordinate distribution is defined by the actual
stage law at that cutoff. `PrefixStage.law_apply_eq_of_disjoint` shows that
later disjoint constraints do not change it, and `marginal_projective` proves
the consistency of all these finite marginals.

Mathlib's Kolmogorov extension theorem then constructs
`BlockProduct.law B hdis`. It is a probability measure; its finite marginals
are exactly the ones just proved consistent; and the intersection of all
block events has measure one. No unspecified infinite measure or consistency
hypothesis is inserted. Equality with the topological support is not needed
for the separating-sequence reduction and is not separately formalized.

For a fixed adaptive transcript, choose a stage containing every block
meeting its queried positions, then telescope back through the later
full-unread-rank blocks. This proves

\[
\rho(C_\pi(v))=P_n(C_\pi(v))
\quad\text{if every block }k\ge n\text{ still has full unread rank at }v.
\]

`BlockProduct.law_inputEvent_eq_of_fullRank` is the exact identity, and
`law_unionEvent_eq_of_fullRank` extends it to unbounded prefix-free stopping
unions.

`BlockProductAnswer` applies the stabilized finite marginals to the parent
and child transcript events. Thus the fair-or-forced law also holds under
the actual infinite measure. In particular, when the next query causes no
block rank drop,

\[
\rho(C_\pi(vb))=\tfrac12\rho(C_\pi(v))\qquad(b=0,1).
\]

This mass identity includes null histories. At a rank drop all parent mass
lies in one child and the other child has mass zero. The corresponding
conditional probabilities are stated separately with the required positive
parent mass.

## Future-block stopping and Borel comparison

`FutureNoDrop` repeats the decreasing-horizon and cylinder-uniqueness argument
for safety in **every** block `k≥j`. It keeps the safety cutoff `j` separate
from the comparison stage `n`, requiring `j≤n`. The resulting equality of
restricted transcript laws compares `ρ` with `P_n` on the event that no
tracked block ever loses rank.

The module also defines `firstDropAfter B j π N` as safety at horizon `N`
minus safety forever. Its numerical characterization says that all tracked
blocks are full rank at `N` and some tracked block has a strict rank decrease
at a one-based query `t>N`. The theorem
`FutureNoDrop.law_firstDropAfter_of_le` proves equality of its `ρ` and `P_n`
probabilities. Taking `n=j+1` compares with the stage already imposing block
`j`, while tracking that block and all later ones. Under the construction's
horizon-avoidance property, this is the event used for the paper's `Aᵢⱼ`
comparison.

`HorizonAvoidance` supplies a concrete finite query set over every branch
through a prescribed horizon. `HorizonLaw` proves equality of the corresponding
finite-answer distributions, then of real and nonnegative extended-real
integrals of arbitrary horizon functionals. In particular it proves equality
of the actual early-wager expectation under `ρ` and the finite stage.

`LateDropBound` combines these comparisons with the Borel `H/L` partition
and the given stage estimates to obtain the late-drop bound. The subsequent
summability and capital argument is documented in the
[stage-estimates note](stage-estimates.md).

## Scope

These results establish the finite-stage cylinder identity, its first-rank-drop
tail transfer, the Borel no-drop restriction identity, and the conditional
fair-or-forced answer law after partial rank loss. They also construct the
infinite block law and prove the corresponding finite-marginal, conditional
answer, Borel restriction, and first-future-drop comparisons. The stage
construction must still supply the quantitative estimates used to control
forced wagers.

No change to the paper's finite-stage formula was required. The formalization
makes explicit the finite support representation, compatibility boundaries,
and the countable disjoint-union argument used to justify it.
