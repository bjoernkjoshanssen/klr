# Base-four KL randomness does not imply binary KL randomness

The extension proves the counterexample under the same total computable-real
strategy convention as the original separation theorem. Its entry point is
[BaseInvariance.lean](../Klr/BaseInvariance.lean):

```lean
theorem Klr.exists_baseFour_random_not_binary_random :
    ∃ X : Klr.Cantor,
      Klr.BaseFour.KolmogorovLovelandRandom (Klr.BaseFour.pairDigits X) ∧
      ¬Klr.KolmogorovLovelandRandom X
```

`pairDigits X n = (X (2*n), X (2*n+1))`. The four symbols are represented by
`Bool × Bool`; numerically the pair `(a,b)` denotes `2*a+b`. Thus the conversion
is the usual grouping of adjacent binary digits into base-four digits.
The formal statement is on digit streams. It does not introduce a separate
real-number expansion API or a definition of randomness directly on `Real`.

The reverse implication is proved, and
`Klr.binary_random_ssubset_baseFour_random` states the resulting proper
inclusion on binary streams under this grouping.

## Strategy definitions and the two simulations

[BaseFour.lean](../Klr/BaseFour.lean) defines four-symbol strategies explicitly:
a total computable query function, freshness on every answer history, and a
uniformly computable nonnegative real capital process starting at one. Its
fairness equation averages over all four possible next digits.

A binary scan is pair-respecting if it starts every pair at an even coordinate
and then queries that coordinate's odd partner, independently of the first
answer. The formal equivalence is

```lean
BaseFour.kolmogorovLovelandRandom_pairDigits_iff (X : Cantor) :
  BaseFour.KolmogorovLovelandRandom (BaseFour.pairDigits X) ↔
    PairRespectingRandom X
```

The forward simulation splits a four-way bet into two binary bets. After the
first bit its capital is the average of the two remaining digit capitals;
after the second bit it equals the original four-symbol capital. Conversely,
restricting a pair-respecting binary strategy to complete pairs gives a
four-symbol strategy. Nonnegative binary fairness bounds the intermediate
capital by twice the capital immediately preceding it, so unbounded success
cannot occur only at intermediate times. Both simulations include the
computability and freshness proofs.

## Why one family of Borel partitions works for both halves

For every prescribed infinite answer sequence, a pair-respecting scan
eventually reads position `2*n` exactly when it eventually reads `2*n+1`.
[PairRespecting.lean](../Klr/PairRespecting.lean) proves this pathwise statement.
It is an assertion about eventual reads: a finite horizon can end between the
two queries.

[ParityPools.lean](../Klr/ParityPools.lean) obtains even pools by prepending
two auxiliary scans that read all even positions and no odd positions. Their
weights in the existing weighted-query construction sum to `3/4`. The
weighted query probability is therefore at least `3/4` at even positions and
at most `1/4` at odd positions. The selected limsup subsequence is eventually
even, and the first auxiliary scan's high set has measure one.

For an error smaller than one, a good pool cannot contain an odd position:
that auxiliary scan would miss it on its entire high set. Removing the two
auxiliary indices gives a good even pool for the original scan family.
Adding one to every member gives an odd pool with exactly the same high and
low events for every pair-respecting scan. The partitions and margin are
unchanged. The shifted pool is still produced by an ordinary fixed program.
The auxiliary scans are used only to select pools; they are not members of
the family of betting strategies protected by the final construction.

This wrapper reuses the original weak-limit, finite-advice, search-termination,
and search-soundness theorems. No new compactness argument is required.

## Stage construction with a retained coordinate restriction

[ConfinedStageConstruction.lean](../Klr/ConfinedStageConstruction.lean) accepts
good pools satisfying an arbitrary coordinate predicate for each stage. The
original sparse-list selection, horizon search, syndrome computation,
reconstruction program, and probability estimates apply to these pools.

[ConfinedStageRecursion.lean](../Klr/ConfinedStageRecursion.lean) retains the
coordinate predicate in the object selected at each recursive step. This
placement matters: weakening the existence statement to the old stage
relation before invoking classical choice would discard confinement.

[ParityConstruction.lean](../Klr/ParityConstruction.lean) uses the predicate
`p % 2 = n % 2` at stage `n`, and enumerates the countable subtype of
pair-respecting strategies. Normalization preserves the scan exactly.
The resulting theorem is already stronger than the construction component
needed for the final counterexample:

```lean
∃ X : Cantor,
  PairRespectingRandom X ∧
  ¬MartinLofRandom (fun n => X (2*n)) ∧
  ¬MartinLofRandom (fun n => X (2*n+1))
```

The enumeration and global stage choices are classical. Each finite
description still runs an ordinary program; no effective enumeration of all
total strategies is assumed.

## Projected tests avoid an extra compiler-length assumption

The supplied proof sketch compresses an affine system to its even or odd
coordinates and invokes a constant additive increase in program length.
That familiar claim needs a suitable universal programming system. The
repository's concrete `AffineDescription.run` encodes a partial-recursive
code and input by a particular natural-number pairing; computability of a
transformation alone does not establish that length bound for this encoding.

[ParityDescription.lean](../Klr/ParityDescription.lean) instead builds two
new Martin-Löf tests using the original program strings. For each parity it:

1. Runs the original affine-description interpreter.
2. Checks validity and the original rank/length budget.
3. Checks a finite truth table showing that the event depends only on the
   selected parity.
4. Enumerates the corresponding event on the half-sequence.

The finite truth-table check is useful because stage reconstruction promises
an equivalent affine event, not a particular zero-column matrix presentation.
Injective coordinate selection preserves fair-coin measure, so the projected
event has exactly the original measure `2^(-rank)`. The original description
budget therefore supplies the required test bound without changing programs
or increasing ranks. Stage `2*n+b` covers test level `n` for half `b`.
The two halves may fail different tests, which is sufficient.

## The even/odd splitting theorem is proved

[Splitting.lean](../Klr/Splitting.lean) proves

```lean
kolmogorovLovelandRandom_even_or_odd (X : Cantor)
    (hX : KolmogorovLovelandRandom X) :
  MartinLofRandom (fun n => X (2*n)) ∨
  MartinLofRandom (fun n => X (2*n+1))
```

This is the even/odd instance of Theorem 12 of Merkle, Miller, Nies, Reimann,
and Stephan, [*Kolmogorov–Loveland Randomness and Stochasticity*](https://people.math.wisc.edu/~jsmiller8/Papers/kl.pdf).
The reference is mathematical provenance; its conclusion is not assumed in
Lean. The proof does not depend on an unproved equivalence between external
partial-real strategies and the repository's convention.

The implementation uses bounded clopen approximations to two failing ML
tests and compares their first witness times. In one orientation, the other
half's witness time provides infinitely many successful finite clopen bets.
Conditional clopen probabilities give rational fair capitals. Finite weighted
sums, a positive reserve, and summable truncation errors yield legal rational
wagers with unbounded capital.

[SplittingScheduler.lean](../Klr/SplittingScheduler.lean) reads additional bits
from the oracle half at zero wager until the next finite computation is ready,
then bets on the next target bit. It proves freshness, progress, and exact
capital agreement and constructs a `PartialBetting.SourceRun`. The existing
proved rational totalization theorem then contradicts binary KL randomness.
The supporting modules are [SplittingClopen](../Klr/SplittingClopen.lean),
[SplittingReserve](../Klr/SplittingReserve.lean), and
[SplittingWitness](../Klr/SplittingWitness.lean).

## Scope and verification

Both bases use total fresh computable scans and uniformly computable real
capital. The extension proves the binary/base-four case. It does not claim
the analogous result for arbitrary pairs of bases or a new equivalence with
every partial computable-real presentation.

The project remains Mathlib-only and uses the existing Lean/Mathlib 4.36.0
pins. The main theorem and strict-inclusion theorem have no construction,
splitting, or effectiveness hypotheses. Their transitive axiom dependencies
are Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.
