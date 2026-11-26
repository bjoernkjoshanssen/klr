# Finite-stage identities and first-rank-drop events

This note records the probability identities used in Sections 3 and 5 of
[Liu–Meng, version 1](https://arxiv.org/abs/2611.31004v1), including the
zero-probability case and the countable stopping-event step. All measures in
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

## Scope

These results establish the finite-stage cylinder identity and its
first-rank-drop tail transfer. They do not construct the final infinite block
measure `ρ`, prove the equality of restrictions to all Borel transcript events
on `T=∞`, or establish the final Borel–Cantelli and martingale convergence
arguments. The conditional fair-or-forced bit law after partial rank loss
also remains to be connected to the existing algebraic fiber and rank-drop
lemmas.

No change to the paper's finite-stage formula was required. The formalization
makes explicit the finite support representation, compatibility boundaries,
and the countable disjoint-union argument used to justify it.
