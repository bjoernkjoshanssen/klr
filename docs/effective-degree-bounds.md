# Effective degree bounds for the KL/ML separation

The effective construction is complete. It produces a separating probability
measure with exact rational cylinder probabilities computable from the fourth
halting jump, and a separating sequence computable from the fifth jump.

The public endpoints are in
[`EffectiveSeparation.lean`](../Klr/EffectiveSeparation.lean):

```lean
Klr.exists_fourthJump_computable_separating_measure
Klr.exists_kolmogorovLovelandRandom_not_martinLofRandom_below_fifthJump
```

They have no remaining stage-construction, partition-effectivity, or
point-selection hypotheses. They use the repository's existing
`KolmogorovLovelandRandom` and `MartinLofRandom` definitions.

Throughout this note, `0^(n)` means the actual `n`-fold halting jump of the
empty oracle, implemented by `OracleJump.zeroJump n`. The notation
`X ≤T 0^(5)` is an upper bound on Turing degree; it does not assert strict
inequality or that this upper bound is optimal.

## The two conclusions

The measure theorem supplies a probability measure `ρ` and a function
`q : List Bool → ℚ` such that:

- `q` is uniformly computable from `0^(4)`.
- For every finite binary string `σ`, the real value of `q σ` is exactly
  `ρ([σ])`.
- For `ρ`-almost every `X`, `X` is KL-random and is not ML-random.

The exact rational assertion is stronger than merely supplying arbitrarily
accurate approximations to the cylinder probabilities. The concrete objects
and their identities are also available directly:

```lean
Klr.EffectiveSeparation.measure
Klr.EffectiveSeparation.cylinderMass
Klr.EffectiveSeparation.cylinderMass_computableIn
Klr.EffectiveSeparation.cylinderMass_eq
Klr.EffectiveSeparation.ofReal_cylinderMass_eq
Klr.EffectiveSeparation.ae_separating
```

The sequence theorem has the following conclusion:

```lean
∃ X : Cantor,
  KolmogorovLovelandRandom X ∧
  ¬ MartinLofRandom X ∧
  Reduces X (OracleJump.zeroJump 5)
```

This is an effective selection of one construction satisfying the separation
argument. The theorem does not say that every block sequence obtainable by
the earlier unrestricted classical choices has a fourth-jump computable law.

## Where the jumps are used

| Object or operation | Proved upper bound | Reason |
| --- | --- | --- |
| Raw simulator scans and rational capital | Ordinary primitive recursive, uniformly in the index | Bounded simulation of every source program, on each of two sides |
| The chosen normalization of these simulators | `0^(2)` | Select the least ordinary approximation program satisfying a Π₂ correctness condition |
| Selected query coordinates and their limits | `0^(2)` | Decide cofinality and emptiness of ordinary c.e. reservoirs |
| Fast L1 names for the weak-limit densities | `0^(3)` | One-jump acceleration of convergent rational prefix tables |
| Clopen names in measure for the fixed high sets | `0^(4)` | A second acceleration, applied to ramps converging to the high-set indicators |
| The complete finite-stage history and output-code sequence | `0^(4)` | Search for finite certificates of strict inequalities, then iterate along valid histories |
| Exact rational cylinder probabilities of the block law | `0^(4)` | A cylinder of length `n` stabilizes at stage `n` |
| A KL-random point satisfying every selected block | `0^(5)` | One-jump selection of positive closed restrictions |

The hierarchy-to-jump proofs are connected to Mathlib's actual relative
computability relation. The relevant foundation is described in
[the oracle and jump note](oracle-jump.md). The upper-bound direction of
Post's theorem suffices: a Πₙ or Σₙ predicate is decidable in the corresponding
iterated jump. A full equivalence between every hierarchy level and relative
enumerability is not needed for these endpoints.

## A uniform family that covers all strategies

The original randomness definition quantifies over total computable-real
betting strategies with fresh, nonmonotone scans. The effective construction
needs one uniformly computable sequence of strategies whose failure implies
failure of every original strategy.

[`UniformStrategyFamily.lean`](../Klr/UniformStrategyFamily.lean) provides this
sequence. It enumerates total simulators of arbitrary ordinary source codes,
with two simulator indices for each code. This avoids any need to recognize
which arbitrary source programs are total.

For an original strategy `s`, the proof first replaces its real capital by a
success-preserving positive rational capital process. It compiles that
process's query and rational wager into one ordinary source program. The
program is fixed before the input sequence is supplied. The existing
two-simulator theorem then gives two fixed family indices whose success
sets cover the whole success set of `s`:

```lean
∃ e₀ e₁, ∀ X,
  s.Succeeds X →
    (UniformStrategyFamily.strategy e₀).Succeeds X ∨
    (UniformStrategyFamily.strategy e₁).Succeeds X
```

Consequently, `kolmogorovLovelandRandom_iff` identifies the existing KL
randomness definition with failure of every indexed simulator. This is
coverage of success sets, which is exactly what the randomness argument
requires.

The finite-stage estimates protect the normalized simulators. The existing
`BettingStrategy.normalize_preserves_success` theorem connects their failure
back to failure of the raw simulators, and the coverage theorem then connects
it to all original strategies.

There is one small change to the original normalization implementation.
`CapitalApproximation.ofComputable` now chooses the least index of a correct
ordinary approximation program. Its interface and error bounds are
unchanged. For a uniformly computable rational family, correctness of a
proposed program is Π₂, so this canonical choice is uniformly computable
from `0^(2)`. Each selected program is still an ordinary program. The
uniformity proof is in
[`CanonicalCapitalApproximation.lean`](../Klr/CanonicalCapitalApproximation.lean),
and [`UniformNormalization.lean`](../Klr/UniformNormalization.lean) carries
the bound through to the exact normalized wagers used by the old stages.

## Selecting scalar query limits in the second jump

The starting data are scalar coordinates of the query indicators:
their integrals over every binary cylinder, together with the weighted query
probability as an additional coordinate. These coordinates are uniformly
left-c.e. and lie in `[0,1]`.

[`EffectiveQueryCoordinates.lean`](../Klr/EffectiveQueryCoordinates.lean)
proves this with actual increasing rational lower approximations. A finite
query horizon gives an exact finite-prefix calculation; truncating the
weighted sum in both strategy index and time gives the weighted coordinate.
These query indicators live on prescribed-answer space, where a horizon of
`V` uses only the first `V` answers. The separate input-space scan algorithms
compute bounds on all queried positions when those bounds are needed.

A reservoir is a tail of the natural numbers intersected with finitely many
strict rational lower constraints on these scalar coordinates. Membership is
ordinary c.e. because all the constraints have finite lower-approximation
witnesses. Cofinality of such a reservoir is Π₂, and emptiness is Π₁.

[`CoordinateRefinement.lean`](../Klr/CoordinateRefinement.lean) uses `0^(2)`
to choose a narrower rational interval for a scheduled coordinate. The lower
constraint preserves an unbounded reservoir; the upper constraint is
certified by emptiness of the corresponding higher-threshold tail. Repeating
this process produces an increasing sequence of positions and shrinking
intervals for every coordinate. The interval chosen at the known stage
`Nat.pair i k` gives a rational approximation to coordinate `i`'s limit with
error at most `2^(-k)`.

[`EffectiveQueryPartition.lean`](../Klr/EffectiveQueryPartition.lean) then
takes an ordinary classical weakly convergent subsequence. This last choice
does not consume an additional jump in the coordinate names: all cylinder
integrals already converge along the selected positions, so uniqueness of
limits identifies the weak limit's cylinder integrals with the previously
named scalar limits. The resulting Borel representatives are bounded between
zero and one.

### Why ordinary pool programs still exist

The selected weighted limit need not be the global limsup of the weighted
query probabilities. The effective route instead retains a useful property
of the finite reservoirs: for every positive error, one ordinary c.e.
reservoir contains all sufficiently late selected positions and has weighted
query probability everywhere at most the limiting value plus that error.

[`EffectivePoolReservoir.lean`](../Klr/EffectivePoolReservoir.lean) proves that
the original pool search can be restricted to such a reservoir. A nonempty
c.e. set has an ordinary primitive-recursive enumeration with repetitions.
The search enumerates candidate pools through that enumeration and applies
the existing finite tests.

The chosen reservoir may have been selected using a jump oracle. Its finite
description still determines an ordinary enumeration program, fixed before
the variable pool-size input. The pool contract retains the quantifier order
“there exists an ordinary program that works at every sufficiently large
size.” This is the property needed by the original short-description proof.

## From cylinder integrals to fourth-jump high-set names

For the bounded weak-limit representative `g_i`, the fixed high set is
`H_i = {X | g_i(X) = 1}`. The effective output is a sequence of actual clopen
sets approximating `H_i` in fair-coin measure. It is not a pointwise oracle
decision procedure for membership in `H_i`.

[`RationalPrefixCode.lean`](../Klr/RationalPrefixCode.lean) represents finite
rational prefix tables by a depth and a finite list of rational values. It
computes their L1 distance exactly as a rational finite average, and proves
that this average equals the actual L1 metric.

Given cylinder-integral names in an oracle `A`, the average value on a
cylinder of depth `d` is `2^d` times its cylinder integral. Taking the integral
approximation at precision `2d` gives a table with error at most `2^(-d)`
relative to the exact prefix-average table. The analytic prefix-average
theorem proves that these tables converge in L1 to `g_i`.

The required acceleration is explicit in
[`Computability/CauchyModulus.lean`](../Klr/Computability/CauchyModulus.lean).
For rational distances computable in `A`, the condition

```text
for all s,t ≥ N, distance(table_s, table_t) ≤ 2^(-k)
```

is Π₁ relative to `A`. The jump `A'` decides it, and ordinary relative search
finds a suitable `N`. Analytic convergence proves that this search succeeds;
no convergence rate is assumed beforehand. Applied to the prefix tables,
this yields fast L1 names for `g_i` in `A'`.

Next use the rational ramps

```text
ramp_m(x) = max(0, 1 - m * (1 - x)).
```

On `x ≤ 1`, these converge to the indicator of `x = 1`. Their Lipschitz
constant is `m`, so applying the `m`th ramp to the density approximation at
precision `2m` still gives convergence in L1. A second Cauchy acceleration
gives fast names for the indicator in `A''`. Thresholding a rational table
at `1/2` produces a clopen set, and its symmetric-difference measure is at
most twice the table's L1 error.

The full generic theorem is
`EffectiveHighSet.exists_highSet_name`. With `A = 0^(2)`, it gives clopen
names in `0^(4)` for the exact fixed partitions used by the pool theorem.
[`EffectiveFixedPartitions.lean`](../Klr/EffectiveFixedPartitions.lean)
packages both facts together: `simulatorHighName` gives the clopen names,
and `computable_pools` gives the ordinary pool-program contract for those
same high sets and normalized scans.

## Searching the original finite-stage requirements

The effective stage search works with genuinely finite candidates. A
candidate contains the pool and matrix data, a horizon, an ordinary binary
program, its affine-code output, and a finite execution bound.

[`FiniteStageCandidate.lean`](../Klr/FiniteStageCandidate.lean) verifies the
ordinary execution using `Nat.Partrec.Code.evaln`. It also checks the affine
certificate, exact event and rank agreement, the requested support cutoff,
and the unchanged short-description inequality:

```text
2 * program.length + stage + 1 ≤ output.rank.
```

The interpreter is exactly `AffineDescription.run`. The fourth-jump oracle
selects which ordinary programs to use; it is not an oracle supplied to
those description programs. Therefore the resulting failed test is the
existing ordinary Martin-Löf test, not a relativized test.

The probability checks use the clopen names, ordinary finite scan
calculations, and exact rational conditioning on the previous affine
constraints. The remaining all-time rank events have clopen approximations
in the first jump, which are already available in `0^(4)`. Finite unions,
intersections, complements, and the relevant observation-map preimages do
not add a jump. Dividing by an exact rational conditioning probability
preserves a computable error bound tending to zero.

[`EffectiveRealApproximation.lean`](../Klr/EffectiveRealApproximation.lean)
provides the strict-inequality certificates. If `q_k` approximates a real
quantity `x` with error `e_k → 0`, the rational test `q_k + e_k < r` certifies
`x < r`. Whenever `x < r`, sufficiently accurate approximations pass the
test. A finite list of strict inequalities has a common sufficient precision.

The wager objective is the exact existing rational finite-stage objective;
[`UniformStageCost.lean`](../Klr/UniformStageCost.lean) proves it computable
already in `0^(2)`. The actual Boolean acceptance predicate in
[`EffectiveStageChecker.lean`](../Klr/EffectiveStageChecker.lean) is thus
uniformly `0^(4)`-computable.

Completeness is obtained by applying the original extension theorem with
half the target error. The resulting margins make every target probability
inequality strict. The checker searches over the candidate, its execution
bound, and its approximation precision. It searches for a finite successful
certificate; it does not need to decide whether an arbitrary candidate will
ever pass.

The invariant-preserving recursion requires successful search only on valid
histories. Neither the validity predicate nor the semantic stage relation
must be decidable. `EffectiveConstruction.concreteRun` supplies the actual
fourth-jump computable run and proves that it satisfies the original stage
estimates at every stage.

## Cylinder probabilities stabilize at a known stage

The cutoff at stage `k` is greater than `k`, greater than the previous block
supports, and greater than every query coordinate on every protected earlier
finite scan branch. In particular, every position in the support of the
`k`th block is at least `k`.

A cylinder `[σ]` of length `n` depends only on positions below `n`. Every
block with index at least `n` therefore leaves this cylinder's probability
unchanged. Its probability under the infinite block law is exactly its
probability after the first `n` blocks.

[`EffectiveBlockProduct.lean`](../Klr/EffectiveBlockProduct.lean) proves this
identity, including equality with the actual infinite product law. The
finite-stage probability is obtained by rational counting under the first
`n` affine output codes. Those codes are uniformly computable in `0^(4)`,
so the exact cylinder function is computable in the same oracle. There is
no search for a stabilization stage and no jump hidden in taking the
infinite product.

## A fifth-jump point from positive closed restrictions

The final selection theorem is specialized to the needs of the separation;
it does not assume a general effective measure-theory library or an
unproved basis theorem.

For each raw simulator index `e` and natural bound `b`, let `C(e,b)` be the
closed set of inputs on which that simulator's capital stays at most `b`
at every time. These sets increase with `b`. Since the measure is almost
surely KL-random, the union over `b` has full measure for every `e`.

The raw simulator capital and scans are uniformly ordinary computable.
Consequently, imposing finitely many such bounds up to a finite time gives
an actual computable clopen set. These clopen sets decrease to the closed
restriction imposing the bounds at all times. Using raw simulators here
also means that normalization does not add to the oracle needed for this
last selection.

Suppose exact rational cylinder masses of a probability measure are
computable in an oracle `A`. The finite clopen restrictions then have exact
rational masses computable in `A`. A history of length `n` is valid when
its closed region has mass at least `4^(-n)`. By continuity from above, this
is equivalent to requiring every finite clopen approximation to have mass
at least `4^(-n)`. That is one universal number quantifier over an
`A`-decidable rational comparison, hence a Π₁(A) condition.

Full measure of each increasing union and a split into the next two prefix
cylinders guarantee that every valid history has a valid extension. The
jump `A'` decides the validity test, chooses an extension, and iterates the
process. Compactness gives a point in all the selected closed regions. Its
bits are already determined by the selected finite prefixes, so the point
itself is computable in `A'`.

The implementation in
[`EffectiveClosedSelection.lean`](../Klr/EffectiveClosedSelection.lean) also
keeps positive measure in every prefix of the resulting point. This places
the point in every full-measure closed set. The affine block events are
closed and have full measure under the block law, so the point satisfies
every block. The original ordinary short descriptions then witness failure
of `AffineDescription.test`.

[`EffectiveKLSelection.lean`](../Klr/EffectiveKLSelection.lean) connects the
selected capital bounds to the original KL randomness definition.
[`EffectiveBlockSeparation.lean`](../Klr/EffectiveBlockSeparation.lean)
combines these facts for a fourth-jump run. Substituting
`EffectiveConstruction.concreteRun` gives the unconditional fifth-jump
separator in `EffectiveSeparation.lean`.

## Verification and scope

The full `lake --wfail build` passes with the repository's pinned Lean and
Mathlib, including the earlier separation and base-four developments. The
endpoint module can also be checked on its own with:

```sh
lake --wfail build Klr.EffectiveSeparation
```

The main endpoints and their logical dependencies can be inspected with:

```lean
import Klr.EffectiveSeparation

#check Klr.exists_fourthJump_computable_separating_measure
#check Klr.exists_kolmogorovLovelandRandom_not_martinLofRandom_below_fifthJump

#print axioms Klr.exists_fourthJump_computable_separating_measure
#print axioms Klr.exists_kolmogorovLovelandRandom_not_martinLofRandom_below_fifthJump
```

Both unconditional endpoint theorems, and the exact cylinder-computability
theorem, report only the standard axioms `propext`, `Classical.choice`, and
`Quot.sound`.

The theorem uses the same total computable-real strategy convention as the
original unconditional separation. The existing partial rational source-run
bridge supplies its previously proved consequence; no equivalence with every
convention for partial computable-real strategies is asserted here. All
construction and selection arguments concern binary Cantor space and require
no identification with real-number expansions.

Classical choice still appears when packaging analytic limits and witnesses.
The relevant effectiveness claims are separate proved `ComputableIn` or
`Reduces` theorems about those selected objects. The result is an upper bound
in the actual halting-jump hierarchy, with no claim of a feasible ordinary
running time or a sharp degree bound.
