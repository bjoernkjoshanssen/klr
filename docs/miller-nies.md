# Partial and total Kolmogorov–Loveland strategies

## What is proved

The repository now contains an explicit, checked totalization of **partial
rational-wager programs**. For every such program, it constructs two total
strategies whose success sets cover every infinite fresh run on which the
partial program succeeds. The output strategies use the existing `ScanRule`,
`CapitalProcess`, `ComputableRealCapital`, and `BettingStrategy` interfaces.
Their queries and rational capital functions are primitive recursive.

The main theorem, in namespace `Klr.PartialBetting`, is:

```lean
theorem two_total_strategies_cover
    {c : Nat.Partrec.Code} {X : Cantor}
    (r : SourceRun c X) (hr : r.Succeeds) :
    (strategy c false).Succeeds X ∨ (strategy c true).Succeeds X
```

The two strategies depend only on the source code `c`. They do not depend on
the input `X`, a successful run, or knowledge of which parity will succeed.
The corollary `no_partial_rational_success` says that a sequence satisfying
the repository's total computable-real definition of KL randomness admits no
successful run of any partial rational-wager program.

This is a substantive special case of the Miller–Nies statement. **It is not
yet a theorem equating the full partial computable-real-capital definition
with the repository's total computable-real-capital definition.** The
remaining source-model bridge is described below.

## Sources and the precise attribution

Miller and Nies, *Randomness and computability: open questions*, Section 6,
immediately following Definition 6.1, state that the success set of a partial
KL test is covered by the success sets of two total tests, and that the latter
may even be taken primitive recursive. They cite reference [30]:

* W. Merkle, *The complexity of stochastic sequences*, Conference on
  Computational Complexity (CCC 2003), pp. 230–235.

The source checked for the explicit construction in this iteration is Laurent
Bienvenu's thesis, *Caractérisations de l'aléatoire par les jeux :
imprédictibilité et stochasticité* (2008), Remark 1.7.7, printed p. 35
(PDF page 57). It splits
the source bets according to the parity of the queried coordinate and uses
free observations of the opposite parity while waiting for the partial
computation. That remark points to a different Merkle paper for further
discussion:

* W. Merkle, *The Kolmogorov–Loveland stochastic sequences are not closed
  under selecting subsequences*, *Journal of Symbolic Logic* 68 (2003),
  1362–1376. DOI:
  [10.2178/jsl/1067620192](https://doi.org/10.2178/jsl/1067620192).

Author-hosted sources:

* [Miller–Nies PDF](https://people.math.wisc.edu/~jsmiller8/Papers/questionsfinal.pdf).
* [Bienvenu thesis PDF](https://www.labri.fr/perso/lbienvenu/docs/publications/bienvenu-phd.pdf).

The full text of Merkle's CCC paper was not obtained in this iteration. The
Lean proof implements and independently verifies the explicit construction
in Bienvenu's exposition; it does not treat the bibliographic citation as a
proof assumption. No error in the totalization argument is claimed here.

## The partial source model

`Action` is the ordinary encodable type

```lean
ℕ × (ℤ × ℕ)
```

Its components are a query position, a signed numerator, and a natural
denominator. A source program receives its previously completed answers as a
finite Boolean list and returns an action, or diverges. Its unbounded
semantics are `partialAction c`; `approximate c` uses Mathlib's actual
bounded evaluator `Nat.Partrec.Code.evaln`.

Two representation results connect the bounded evaluator to ordinary partial
recursion:

* `exists_partialAction`: every partial recursive function from finite
  Boolean lists to `Action` has a representing program code.
* `approximate_complete`: an action belongs to the unbounded computation
  exactly when some finite evaluator budget returns that action.

Thus the hypotheses are not an assumed total simulator or an assumed
success-preserving map. The simulator is constructed from an arbitrary
program code and its correctness is proved from the evaluator semantics.

The decoded fraction is

\[
 f(a)=\max\bigl(-1,\min(1,\operatorname{num}(a)/\operatorname{den}(a))\bigr).
\]

Division by zero uses the rational field convention and gives zero. Clipping
makes every code output a legal wager, so even malformed programs produce
legal total output strategies. `fraction_eq_of_legal` proves that clipping
does not alter a fraction already in `[-1,1]`. For an answer `b`, the capital
multiplier is `1 + f(a)` when `b = true` and `1 - f(a)` when `b = false`.

`SourceRun c X` consists of an action sequence, evidence that each action is
eventually produced on the previous source answers from `X`, and injectivity
of its queried coordinates. Freshness is required along this source run;
the program may diverge or behave badly on other transcripts. The output
strategies remain total and fresh on **all** finite transcripts.

Source success means unbounded finite capital, exactly as for
`BettingStrategy.Succeeds`. No assumption of convergence to infinity, a
positive reserve, or strictly positive individual return factors is used.

## The scheduler and cached-answer replay

The even simulator wagers only on even coordinates; the odd simulator wagers
only on odd coordinates. Each stores three pieces of information:

1. The completed simulated assignment, in chronological order.
2. Every genuinely observed input bit, including free observations made while
   waiting for a computation.
3. The current bounded-evaluation budget for the next source action.

On every finite outward transcript the next step is completely determined.

| Bounded source computation | Genuine outward query | Simulated progress | Wager |
| --- | --- | --- | --- |
| No action yet | A fresh inactive coordinate | Increase the computation budget | Zero |
| Ready action at an unseen coordinate | That coordinate | Append its answer and reset the budget | Source fraction on active parity; zero otherwise |
| Ready action at a cached coordinate | A fresh inactive coordinate | Replay the cached answer and reset the budget | Zero |

The final row is necessary: while waiting, the simulator may have read an
inactive coordinate that the source later requests. Reading that coordinate
again would violate the definition of `ScanRule`. Replaying its cached
answer completes the source step without a repeated observation.

Fresh filler coordinates are selected by a simple explicit bound on all
coordinates in the cache. Therefore there is always another unused inactive
coordinate. Each outward step performs only bounded computation and at most
one simulated source action; it never waits for a potentially divergent
source computation before issuing its next query.

## What the correctness theorems establish

`Klr/PartialBetting.lean` proves the machine properties independently of
capital:

* `scan c side` is a genuine total `ScanRule`. Its query function is
  primitive recursive and every query is fresh, including on branches where
  the source computation never returns.
* `run_cache_correct` proves that every cached answer is the corresponding
  bit of the actual input.
* `ActiveCovered` and its preservation theorem prove that every cached
  active coordinate has already been supplied to the source. Consequently,
  source freshness prevents a forthcoming active bet from being skipped as
  a cached observation.
* `completes_next` proves liveness for each halting source action, despite
  arbitrary computation time and cached-answer replay.
* `reaches_source_stage` embeds every finite stage of an infinite source run
  into the actual total run.

`Klr/PartialBettingCapital.lean` adds the capital argument. The rational
capital function is nonnegative, starts at one, and satisfies fairness on
every finite transcript, not merely along the successful source run.
`completes_next_capital` proves that the simulator's capital is multiplied
by exactly the selected source factor when that action completes. Waiting
steps and cached replay have multiplier one.

For source stage `n`, write

\[
 C_0(n)=\prod_{i<n,\ q_i\text{ even}}(1+\epsilon_i f_i),\qquad
 C_1(n)=\prod_{i<n,\ q_i\text{ odd}}(1+\epsilon_i f_i),
\]

where `εᵢ` is `1` for a true answer and `-1` for a false answer.
`reaches_source_capital` proves that each simulator reaches a stage with
capital exactly `C₀(n)` or `C₁(n)`, respectively. `sourceCapital_eq_mul`
proves `C(n) = C₀(n) C₁(n)`. Since the factors are nonnegative, two bounded
parity-capital sequences would give a bounded original capital sequence.
This proves the two-strategy success-covering result for unboundedness,
without a convergence assumption.

`Klr/ComputableRational.lean` supplies the arithmetic needed to finish the
effective statement. It gives rational numbers a primitive-recursive
canonical encoding, proves primitive-recursive rational arithmetic and
comparison, and connects rational functions to the existing canonical
numerator/denominator witnesses in `ComputableRealCapital`. Consequently
the final `strategy` values inhabit the repository's existing
`BettingStrategy` type. No alternative weaker notion of total strategy is
substituted at the end.

## Remaining scope

The source wagers in this proof are rational values delivered by a partial
recursive action program. The existing total-strategy definition allows
arbitrary uniformly computable real-valued capital. We have not yet
formalized a general partial computable-real-capital interface and a
success-preserving conversion from that interface to the rational-wager
source model.

A proof of that bridge must control approximation errors over the whole
run, including bets whose losing return is very small. Simply rounding each
wager with a fixed absolute accuracy does not provide the required
multiplicative capital comparison. A reserve together with suitably
controlled rational approximations is a natural route, but that argument
is not presently a theorem in these modules.

Accordingly, the repository proves the explicit partial-rational to
total-computable-real success-covering reduction and its KL-randomness
corollary. It does not yet claim the full equivalence of all customary
partial and total real-capital presentations of KL randomness.
