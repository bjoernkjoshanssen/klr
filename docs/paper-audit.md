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
There is currently no Lean theorem asserting existence of a KL-random sequence
that is not ML random.

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

The present definition follows the paper's total formulation. The conversion
from partial tests is not yet a Lean theorem here. A complete formalization of
the conventional partial-strategy statement should include that conversion or
state the total formulation explicitly.

Primary source: [Miller–Nies paper](https://people.math.wisc.edu/~jsmiller8/Papers/questionsfinal.pdf).

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

**Still required:** use these algebraic facts to prove conditional probability
statements under uniform affine block measures, and then under an adaptive
transcript. Compatibility cannot be omitted: an impossible history has no
conditional bit distribution of the intended kind.

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

**Still required for the full strategy lemma:** connect the analytic sequence
results to the computable strategy structures, construct the rational reserve
approximation, and prove that the resulting scan/capital pair is a total
computable strategy with the required success-set inclusion.

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
On fair queries, square-summable increments give an `L²`-bounded martingale.
Its convergence and the summable forced wagers bound log capital from above.

**Formal status:** the product law, adaptive conditional-fairness statement,
stopping-event identities, and final almost-sure boundedness argument remain.
The existing finite transcript theorem is an initial component, not a substitute
for these measure comparisons.

## Suggested dependency order

1. Finish the effective, strategy-level version of Lemma 2 and the standard
   implication ML randomness ⇒ KL randomness. The definitions and transcript
   law are now available.
2. Build uniform finite affine-block laws and prove their adaptive observation
   and first-rank-drop identities.
3. Prove the probabilistic construction of sparse rank-preserving lists, using
   the existing incidence/weight estimate downstream.
4. Formalize the computable pool lemma, preserving the order of its
   non-effective finite choices and its effective search.
5. Encode the stage construction and its actual descriptions, including the
   reconstruction of horizons and syndromes.
6. Construct the final measure and prove almost-sure KL randomness and support
   inclusion in one ML test.
7. Finish the separating-sequence theorem and the partial/total formulation
   bridge, then audit the axioms of the final theorem.

The first two stages provide further independent checks of the probability and
effectivity interfaces before undertaking the longest construction arguments.

## Why this is independent of `tt-auto`

The `tt-auto` repository contains useful Cantor-space and arithmetic-hierarchy
infrastructure, but its hierarchy is built around the degree-rigidity project's
relative recursion machinery. No small, ready-made ML-randomness development
was found there. Direct use of Mathlib's `REPred`, program codes, finite linear
algebra, and probability library gives this project a smaller dependency
surface and leaves the earlier project unchanged.

## References

- [Liu–Meng, arXiv:2611.31004v1](https://arxiv.org/abs/2611.31004v1).
- [Miller–Nies, *Randomness and computability: open questions*](https://people.math.wisc.edu/~jsmiller8/Papers/questionsfinal.pdf), especially Section 6.
- [Mathlib v4.36.0](https://github.com/leanprover-community/mathlib4/tree/v4.36.0).
- [`tt-auto`](https://github.com/bjoernkjoshanssen/tt-auto), inspected for reusable foundations, not imported.
