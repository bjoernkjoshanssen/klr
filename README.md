# KL and Martin-Löf randomness

A Lean formalization project investigating Chenghua Liu and Boning Meng,
[*Separating Kolmogorov–Loveland randomness from Martin-Löf randomness*](https://arxiv.org/abs/2611.31004),
version 1, 23 November 2026.

**Status: the separation theorem is proved for the repository's total
computable-real strategy convention.** The actual simultaneous stage
construction, bounded-advice horizon search, computed syndrome, short
reconstruction programs, and infinite-sequence assembly discharge every
construction hypothesis. The project also proves `MLR → KLR`, hence proper
inclusion of the two defined classes. No part of the construction or the
paper's conclusion is assumed as an axiom.

[Separation.lean](Klr/Separation.lean) proves the assumption-free theorem
`Klr.exists_kolmogorovLovelandRandom_not_martinLofRandom`:

```lean
∃ X : Klr.Cantor,
  Klr.KolmogorovLovelandRandom X ∧ ¬ Klr.MartinLofRandom X
```

`KolmogorovLovelandRandom` uses total strategies with uniformly computable real
capital. The partial-program development implements Merkle's even/odd
totalization for rational wagers, including cached-answer replay and an exact
capital simulation. Its precise scope is recorded in the
[Miller–Nies note](docs/miller-nies.md). Total computable-real strategies now
have a proved success-preserving rational normalization. A general partial
computable-real source interface and its conversion remain separate obligations.
Thus the completed theorem should be read with this explicit convention; it
does not silently claim an additional equivalence with every partial-real
presentation of KL randomness.

## The completed construction

The fixed Borel partitions from Lemma 3 are chosen before any stages. At each
stage, one sufficiently large rank simultaneously gives a candidate meeting
all probability estimates and a short program producing that exact affine
event. The program has only the rank, a polynomially bounded candidate index,
and a bounded horizon-advice integer as variable input. It computes the pool,
horizon, syndrome, and certificate. The global recursion preserves all earlier
supports and all previously protected finite horizons.

The main entry points are:

| Result | Checked content |
| --- | --- |
| [StagePrepared](Klr/StagePrepared.lean) | Fixes the reconstruction program before choosing a rank satisfying the candidate estimates and actual binary length budget |
| [StageOneStep](Klr/StageOneStep.lean) | Produces a concrete block, actual horizon, all four probability bounds, and a successfully evaluated short exact affine description |
| [StageRecursion](Klr/StageRecursion.lean) | Constructs coherent finite histories and their infinite diagonal sequence; protects every earlier horizon and obtains each strategy's eventual estimates |
| [StageConstruction](Klr/StageConstruction.lean) | Supplies the actual extension at every stage, removing the recursion's extension premise |
| [Separation](Klr/Separation.lean) | Proves a separating sequence, inequality of the classes, and proper inclusion of MLR in KLR |

The [stage-construction note](docs/stage-construction.md) explains the
quantifier order, finite rational computations, and the distinction between
classical global choices and the ordinary programs needed for short descriptions.

## What is implemented

| Module | Content |
| --- | --- |
| [Cantor](Klr/Cantor.lean) | Cantor space, clopen cylinders, an actual infinite product fair-coin measure, and cylinder measures |
| [EffectiveOpen](Klr/EffectiveOpen.lean) | Effectively open classes using Mathlib's `REPred`, uniform families, and equivalence with a single program recognizing pairs `(level, string)` |
| [EffectiveSearch](Klr/EffectiveSearch.lean) | Existential closure of c.e. predicates by a proved dovetailing search over witnesses and computation stages |
| [MartinLof](Klr/MartinLof.lean) | Martin-Löf tests and randomness, the standard set-based characterization, null test-failure sets, almost-everywhere randomness, and existence |
| [Betting](Klr/Betting.lean) | Total adaptive scan rules, uniformly computable real capital, fairness, unbounded-success semantics, and KL randomness implying computable randomness |
| [ComputableNonrandom](Klr/ComputableNonrandom.lean) | The uniformly effective prefix test proving every computable sequence is not ML random |
| [ScanMeasure](Klr/ScanMeasure.lean) | Exact input-space characterization of a transcript and the fair-coin transcript law |
| [FiniteMeasure](Klr/FiniteMeasure.lean) | Uniform finite-coordinate laws in bits and `ZMod 2`, exact cardinality-to-probability formulas, and disjoint-coordinate independence |
| [Affine](Klr/Affine.lean) | Affine fibers, the count `2^(m-r)` of parity-system solutions, solution fraction `2^-r`, equal-size answer fibers, and the forced-answer/rank-drop criterion |
| [AffineObservation](Klr/AffineObservation.lean) | Residual syndrome fibers after observation, equal completion counts, and the exact factor for any observed background |
| [FiniteStage](Klr/FiniteStage.lean) | Exact probability and conditional-measure identities, including zero-probability transcript events |
| [AffineBlock](Klr/AffineBlock.lean) | Actual finite supports, full unread rank, and the stage identity for old constraints and a disjoint new block |
| [AffineFamily](Klr/AffineFamily.lean) | Positive product probabilities for disjoint blocks and preservation of transcript probabilities after adding a full-unread-rank constraint |
| [StoppingTranscript](Klr/StoppingTranscript.lean) | Prefix-free stopping transcripts, countable disjoint-union transfer, and preservation of unbounded first-rank-drop tails |
| [RemainingRank](Klr/RemainingRank.lean) | Numerical remaining rank, its monotonicity, and exact identification of the stopping event with the first strict rank decrease |
| [AffineAnswer](Klr/AffineAnswer.lean) | Conditional next-answer probabilities on compatible adaptive histories, including partial rank loss: fair iff no rank drop, otherwise forced; supported by [algebra](Klr/AffineAnswerAlgebra.lean) and [measure](Klr/AffineAnswerMeasure.lean) modules |
| [NoDrop](Klr/NoDrop.lean) | Equality of old/new transcript measures restricted to no rank drop ever, for all Borel transcript events |
| [PrefixStage](Klr/PrefixStage.lean) | Actual prefix stage laws, positive conditioning events, and finite-stage telescoping for full-rank transcripts and disjoint-coordinate events |
| [BlockProduct](Klr/BlockProduct.lean) | An actual infinite probability law from proved coherent marginals, almost-sure satisfaction of every block, and exact infinite/finite transcript comparison |
| [FutureNoDrop](Klr/FutureNoDrop.lean) | Infinite/finite Borel restriction identities and first-drop tails for all blocks beyond a specified index, with separate safety and comparison-stage cutoffs |
| [BlockProductAnswer](Klr/BlockProductAnswer.lean) | Actual fair-or-forced next-bit laws under the infinite measure, including zero-mass histories in the child-cylinder identities |
| [ComputableRational](Klr/ComputableRational.lean) | Canonical rational codes, primitive recursive arithmetic, and the bridge to uniformly computable real capital |
| [PartialBetting](Klr/PartialBetting.lean) | A bounded-computation scheduler with primitive recursive fresh queries, cached answers, and liveness on every infinite partial source run |
| [PartialBettingCapital](Klr/PartialBettingCapital.lean) | Fair parity-restricted capital, exact simulation of each parity factor, and success coverage for partial rational-wager programs |
| [Normalization](Klr/Normalization.lean) | The finite telescoping estimate and the infinite bound `∑ h_t² ≤ 1/2` from Lemma 2 |
| [NormalizationSuccess](Klr/NormalizationSuccess.lean) | The full analytic damping step: a positive reserve and unbounded original capital imply unbounded normalized capital |
| [EffectiveNormalization](Klr/EffectiveNormalization.lean) | A computable rational fair approximation with reserve at least `1/4`, uniform additive error, and preserved success |
| [EffectiveNormalizationStrategy](Klr/EffectiveNormalizationStrategy.lean) | Complete strategy-level Lemma 2: same scan, positive rational capital, success preservation, and `∑ wager² ≤ 1/2` on every input |
| [EffectiveScan](Klr/EffectiveScan.lean) | Uniformly effective input events from computable conditions on adaptive transcripts |
| [MaximalInequality](Klr/MaximalInequality.lean) | The actual fair-coin bound `λ{∃ n, capital(n) > 2^m} ≤ 2^-m` for every fresh scan |
| [MLImpliesKL](Klr/MLImpliesKL.lean) | One genuine ML test covering each strategy's entire success set, and Martin-Löf randomness implying KL randomness |
| [StrategyCountability](Klr/StrategyCountability.lean) | Countability of the actual total computable-real strategy type and the almost-everywhere quantifier interchange, without an effective enumeration assumption |
| [FairForced](Klr/FairForced.lean) | Almost-sure bounded capital from fair child-cylinder probabilities and summable forced wagers, using a maximal inequality and exact product factorization |
| [BlockRandomness](Klr/BlockRandomness.lean) | The actual block-law reduction to almost-sure KL randomness and conditional separation from a genuine ML-test cover; the construction obligations remain explicit |
| [DropEvents](Klr/DropEvents.lean) | Actual per-block rank-drop events, measurability of finite-transcript functionals, and finitely many drops in every finite block |
| [EarlyLateWagers](Klr/EarlyLateWagers.lean) | Equation (11) from summable late-drop probabilities and early-wager expectations, using Borel–Cantelli and handling arbitrary finite initial exceptions |
| [HorizonAvoidance](Klr/HorizonAvoidance.lean) | Explicit finite enumeration of every query on every branch through a finite horizon, with full unread rank for supports avoiding those positions |
| [HorizonLaw](Klr/HorizonLaw.lean) | Infinite/finite equality of finite-answer distributions and horizon-functional integrals, including the actual early-wager expectation |
| [LateDropBound](Klr/LateDropBound.lean) | The actual infinite-law late-drop bound from the finite-stage partial-rank, first-drop, and Borel partition estimates |
| [StageErrorBudget](Klr/StageErrorBudget.lean) | Exact dyadic tail sums and the paper's summable `8e_j` and `4e_j` bounds |
| [StageEstimates](Klr/StageEstimates.lean) | The stage contract and the modular implication from estimates (6)–(9) plus effective description cover to separation; the completed construction supplies its hypotheses |
| [DescriptionBudget](Klr/DescriptionBudget.lean) | The summation and measure budget for plain binary program descriptions, with a genuine ML test for any uniformly c.e. family satisfying those budgets |
| [Sparse](Klr/Sparse.lean) | The finite incidence, Cauchy–Schwarz, and averaging estimates used to bound total wagers on candidate supports |
| [FiniteProbability](Klr/FiniteProbability.lean) | Actual uniform finite counting probabilities, expectations, product-sample independence, and Markov/union bounds |
| [UniformSupport](Klr/UniformSupport.lean) | Exact inclusion probabilities, intersection mean and variance, and the small-intersection tail, from [binomial counts](Klr/UniformSupportCount.lean) |
| [RandomMatrix](Klr/RandomMatrix.lean) | Exact annihilator probabilities, restricted rank-failure bounds, and uniform conditioning on full row rank, supported by [linear algebra](Klr/RandomMatrixAlgebra.lean) |
| [SampleConcentration](Klr/SampleConcentration.lean) | Exact count-generating functions, exponential tails, and simultaneous finite sampling bounds |
| [SparseCandidateList](Klr/SparseCandidateList.lean) | Lemma 4's eventual list existence, combining the [actual candidate experiment](Klr/SparseCandidate.lean) and proved [polynomial parameter bounds](Klr/SparseParameters.lean) |
| [SparseCandidateWeights](Klr/SparseCandidateWeights.lean) | The list's incidence-to-weight bridge and a rank-preserving candidate with support weight at most `(2m/M)/(1−θ) * sqrt(MC)` |
| [SparseListConstruction](Klr/SparseListConstruction.lean) | Actual partial-recursive exhaustive list construction, its full specification, and termination for every sufficiently large rank; includes the concrete-code bridge and finite verifier |
| [SparseListWeights](Klr/SparseListWeights.lean) | Direct average and rank-preserving small-weight selection for the actual executable list output, with no reverse conversion to abstract candidates |
| [PoolQuery](Klr/PoolQuery.lean) | Actual query indicators on prescribed answer space, measurable coverage fractions, and finite-horizon L1 convergence |
| [PoolWeakLimit](Klr/PoolWeakLimit.lean) | Simultaneous weak subsequences for countably many Hilbert unit-ball sequences, preserving scalar convergence and the L2 interval bounds |
| [PoolPartitionQuery](Klr/PoolPartitionQuery.lean) | Actual fixed Borel partitions from query indicators, bounded representatives, high-miss convergence, and one rational low-set margin for any finite protected prefix |
| [PoolWeighted](Klr/PoolWeighted.lean) | Actual weighted query probabilities, geometric truncation bounds, a limsup subsequence, and its preservation by the common weak-limit extraction |
| [PoolApproximationFunction](Klr/PoolApproximationFunction.lean) | Borel-event approximation and rational finite-prefix L1 approximation, with a common depth and unit-interval table values |
| [PoolAdviceMeasure](Klr/PoolAdviceMeasure.lean) | Exact identification of the three computable rational pool tests with actual fair-coin measures and integrals |
| [PoolSelection](Klr/PoolSelection.lean) | Distinct finite selections satisfying arbitrary eventual side conditions and the centered-average bound `4/M + ε` |
| [PoolAcceptance](Klr/PoolAcceptance.lean) | Actual accepted candidates at every sufficiently large pool size, from weak selection and finite-horizon convergence |
| [PoolSoundness](Klr/PoolSoundness.lean) | Every accepted pool has the required high/low error bounds, using the final weighted-coverage gap and Markov's inequality |
| [PoolConstruction](Klr/PoolConstruction.lean) | Complete Lemma 3: partitions chosen before stage parameters, rational margin and an ordinary program chosen before M, eventual halting, and exact missed-position bounds |
| [AffineCode](Klr/AffineCode.lean) | Computable right-inverse verification and exact `2^-r` event measure, with [prefix checking](Klr/AffineCodePrefix.lean) and [coverage of every affine block](Klr/AffineCodeCoverage.lean) |
| [SparseSearch](Klr/SparseSearch.lean) | Executable certificate-free full/restricted rank checks and partial-recursive certificate completion, with exact algebraic correctness and halting criteria |
| [AffineDescription](Klr/AffineDescription.lean) | An actual binary program/input interpreter, uniformly c.e. affine cylinder enumeration, and a genuine Martin-Löf test with the proved plain-description budget |
| [AffineProgramLength](Klr/AffineProgramLength.lean) | Explicit compiler length bounds and eventual rank budgets for polynomially bounded input and paired advice |
| [AffineDescriptionSeparation](Klr/AffineDescriptionSeparation.lean) | Modular separation using the implemented interpreter, instantiated by the stage estimates and actual short programs from the completed construction |

These definitions enforce **uniform** effectiveness. It would be incorrect to
define a Martin-Löf test merely by requiring each level separately to be
effectively open. The program-code representation is proved equivalent to the
usual uniformly effectively open formulation; it is not a restriction to a
chosen list of tests.

The only direct library dependency is **Mathlib**. The probability,
computability, and arithmetic developments are all contained in this repository
or Mathlib.

The [finite-stage note](docs/finite-stage.md) explains the exact measure identity,
how the adaptive transcript is represented, why the countable first-drop
transfer has no finite stopping-time bound, and how no-drop equality extends
from cylinders to all Borel transcript events.

The [stage-estimates note](docs/stage-estimates.md) states the construction's
precise output contract and explains the checked reduction from those estimates
and descriptions to a separating sequence.

The [sparse-candidate note](docs/sparse-candidates.md) follows the proof of
Lemma 4 from uniform support and matrix counts through effective exhaustive
search. The [affine-description note](docs/affine-descriptions.md) explains
the concrete test, certificate completion, and program-length bounds.

The [computable-pool note](docs/computable-pools.md) follows Lemma 3 from
the fixed Borel partitions through finite advice, executable search,
eventual halting, and soundness for every accepted pool. It records the
precise quantifier order and the distinction between prescribed answer
space and adaptive input-space transcripts.

## Build and proof checks

The repository retains its original **Lean 4.36.0 / Mathlib 4.36.0** pins.
With [Elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get
lake build
```

`Klr.lean` imports every mathematical module. The GitHub Actions workflow builds
the library and audits the transitive axioms of declarations under `Klr`.
Only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` are allowed.
Unfinished work is recorded in documentation; it is not represented by `sorry`
or additional axioms.

For example, after `import Klr`, these checks expose the dependencies of several
central results:

```lean
#print axioms Klr.ae_martinLofRandom
#print axioms Klr.not_martinLofRandom_of_computable
#print axioms Klr.ScanRule.fairCoin_transcript
#print axioms Klr.Affine.forced_iff_rank_drop
#print axioms Klr.AffineBlock.finiteStage_identity
#print axioms Klr.AffineBlock.nextStageLaw_transcript
#print axioms Klr.StoppingTranscript.finiteStage_rankDropTail_preserved
#print axioms Klr.StoppingTranscript.nextStage_strictRankDropTail
#print axioms Klr.AffineAnswer.stage_next_answer_fair_iff_no_rank_drop
#print axioms Klr.NoDrop.nextStage_map_restrict_noDrop
#print axioms Klr.BlockProduct.law_inputEvent_eq_of_fullRank
#print axioms Klr.FutureNoDrop.law_firstDropAfter_of_le
#print axioms Klr.BlockProductAnswer.child_mass_of_not_forced
#print axioms Klr.PartialBetting.two_total_strategies_cover
#print axioms Klr.tsum_normalizedWager_sq_le_half
#print axioms Klr.normalization_preserves_unbounded_capital
#print axioms Klr.BettingStrategy.normalize_preserves_success
#print axioms Klr.BettingStrategy.normalize_wagers_tsum_le_half
#print axioms Klr.MartinLofRandom.kolmogorovLovelandRandom
#print axioms Klr.BettingStrategy.ae_not_succeeds_of_fair_forced
#print axioms Klr.BlockRandomness.ae_kolmogorovLovelandRandom_of_forced_summable
#print axioms Klr.EarlyLateWagers.ae_summable_forcedWager_of_bounds
#print axioms Klr.StageEstimates.ae_summable_forcedWager
#print axioms Klr.exists_separating_of_stage_estimates_and_descriptions
#print axioms Klr.SparseCandidateList.eventually_exists_goodList
#print axioms Klr.SparseListConstruction.eventually_construct_good
#print axioms Klr.PoolConstruction.exists_fixed_partitions_computable_pools
#print axioms Klr.AffineDescription.rePred_W
#print axioms Klr.AffineDescription.per_program_bound
#print axioms Klr.AffineProgramLength.eventually_programFor_pair_advice_length_budget
#print axioms Klr.exists_separating_of_stage_estimates_and_affine_programs
#print axioms Klr.StagePrepared.Prepared.to_step
#print axioms Klr.StageConstruction.exists_sequence
#print axioms Klr.exists_kolmogorovLovelandRandom_not_martinLofRandom
#print axioms Klr.martinLofRandom_ssubset_kolmogorovLovelandRandom
```

## Scope and further work

The separation theorem has no stage-estimate, reconstruction, program-length,
or effectiveness premise. The older conditional reductions remain useful as
modular APIs, and the construction now supplies their witnesses.

The remaining scope issue is a separate source-model bridge for general partial
computable-real strategies. The rational-wager partial-program development
and the total computable-real normalization are already proved, but the project
does not conflate them with such a bridge. Independent review of that convention
and of the mathematical encoding remains valuable.

The corollary `exists_not_martinLofRandom_no_partial_rational_success` already
shows that the separating sequence defeats every infinite fresh run of a
partial rational-wager source program. The outstanding bridge specifically
concerns general partial computable-real capital, not all partial strategies.

The [audit and formalization roadmap](docs/paper-audit.md) explains which parts
of the paper were checked informally, which components are already in Lean,
and how the stage construction is represented. No mathematical correction to
the paper's stage argument was needed. The formalization uses a stronger finite
wager objective and explicit exhaustive code reconstruction, with the same
required estimates and description budget.
