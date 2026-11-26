# KL and Martin-Löf randomness

A Lean formalization project investigating Chenghua Liu and Boning Meng,
[*Separating Kolmogorov–Loveland randomness from Martin-Löf randomness*](https://arxiv.org/abs/2611.31004),
version 1, 23 November 2026.

**Status: foundations and several intermediate arguments are proved. The
separation theorem is not yet formalized.** This repository does not assume the
paper's conclusion, its pool lemma, or its construction as axioms.

The intended target is

```lean
∃ X : Klr.Cantor,
  Klr.KolmogorovLovelandRandom X ∧ ¬ Klr.MartinLofRandom X
```

`KolmogorovLovelandRandom` currently uses the paper's total-strategy formulation.
The equivalence with the usual partial-strategy presentation is identified in
the [audit and roadmap](docs/paper-audit.md), but has not been formalized here.

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
| [Affine](Klr/Affine.lean) | Affine fibers, the count `2^(m-r)` of parity-system solutions, solution fraction `2^-r`, equal-size answer fibers, and the forced-answer/rank-drop criterion |
| [Normalization](Klr/Normalization.lean) | The finite telescoping estimate and the infinite bound `∑ h_t² ≤ 1/2` from Lemma 2 |
| [NormalizationSuccess](Klr/NormalizationSuccess.lean) | The full analytic damping step: a positive reserve and unbounded original capital imply unbounded normalized capital |
| [DescriptionBudget](Klr/DescriptionBudget.lean) | The summation and measure budget for plain binary program descriptions, with a genuine ML test for any uniformly c.e. family satisfying those budgets |
| [Sparse](Klr/Sparse.lean) | The finite incidence, Cauchy–Schwarz, and averaging estimates used to bound total wagers on candidate supports |

These definitions enforce **uniform** effectiveness. It would be incorrect to
define a Martin-Löf test merely by requiring each level separately to be
effectively open. The program-code representation is proved equivalent to the
usual uniformly effectively open formulation; it is not a restriction to a
chosen list of tests.

The development depends directly on Mathlib. It does not import the much larger
`tt-auto` project. Its computability foundations were inspected, but a small
standalone development using `REPred` avoids bringing the degree-rigidity
development into this project.

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
#print axioms Klr.tsum_normalizedWager_sq_le_half
#print axioms Klr.normalization_preserves_unbounded_capital
```

## What remains

The major outstanding obligations are the effective normalization of strategies,
the adaptive affine conditional-law and stopping-event lemmas, the computable
pool lemma, existence of sparse rank-preserving candidate lists, the stage
construction with explicit program-length bounds, and the final product-measure
argument. The standard implication ML randomness ⇒ KL randomness also remains
to be connected to the new definitions.

The [audit and formalization roadmap](docs/paper-audit.md) explains which parts
of the paper were checked informally, which components are already in Lean,
and why the remaining work is substantial. No error in the paper was identified
in the initial informal audit; that is not a formal verification of its theorem.
