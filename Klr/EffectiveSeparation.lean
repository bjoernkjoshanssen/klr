module

public import Klr.EffectiveConstruction
public import Klr.EffectiveBlockSeparation

/-!
# Effective degree bounds for KL/ML separation

The concrete fourth-jump stage search supplies a separating probability law
with uniformly fourth-jump computable exact rational cylinder masses. The
one-jump positive-closed-class selector then supplies a separator below the
fifth jump. These endpoints have no remaining construction or effectivity
hypotheses and use the repository's existing randomness definitions.
-/

@[expose] public section

noncomputable section

namespace Klr.EffectiveSeparation

open MeasureTheory _root_.Klr.Computability

local instance : Encodable ℚ := (inferInstance : Primcodable ℚ).toEncodable

/-- The probability law of the actual fourth-jump selected affine blocks. -/
def measure : Measure Cantor := EffectiveBlockSeparation.law EffectiveConstruction.concreteRun

instance : IsProbabilityMeasure measure := by
  unfold measure
  infer_instance

/-- Exact rational cylinder masses, with length as the stabilization stage. -/
def cylinderMass : List Bool → ℚ :=
  EffectiveBlockSeparation.cylinderMass EffectiveConstruction.concreteRun

theorem cylinderMass_computableIn :
    ComputableIn {oracleFunction (OracleJump.zeroJump 4)} cylinderMass :=
  EffectiveBlockSeparation.cylinderMass_computableIn EffectiveConstruction.concreteRun

theorem cylinderMass_eq (σ : List Bool) :
    (cylinderMass σ : ℝ) = measure.real (cylinder σ) :=
  EffectiveBlockSeparation.cylinderMass_eq EffectiveConstruction.concreteRun σ

theorem ofReal_cylinderMass_eq (σ : List Bool) :
    ENNReal.ofReal (cylinderMass σ : ℝ) = measure (cylinder σ) :=
  EffectiveBlockSeparation.ofReal_cylinderMass_eq EffectiveConstruction.concreteRun σ

theorem ae_separating :
    ∀ᵐ X ∂measure, KolmogorovLovelandRandom X ∧ ¬MartinLofRandom X :=
  EffectiveBlockSeparation.ae_separating EffectiveConstruction.concreteRun

end Klr.EffectiveSeparation

namespace Klr

open MeasureTheory _root_.Klr.Computability

local instance : Encodable ℚ := (inferInstance : Primcodable ℚ).toEncodable

/-- A separating probability measure with uniformly fourth-jump computable
exact rational cylinder probabilities. -/
theorem exists_fourthJump_computable_separating_measure :
    ∃ (ρ : Measure Cantor) (q : List Bool → ℚ), IsProbabilityMeasure ρ ∧
      ComputableIn {oracleFunction (OracleJump.zeroJump 4)} q ∧
      (∀ σ, ENNReal.ofReal (q σ : ℝ) = ρ (cylinder σ)) ∧
      ∀ᵐ X ∂ρ, KolmogorovLovelandRandom X ∧ ¬MartinLofRandom X :=
  ⟨EffectiveSeparation.measure, EffectiveSeparation.cylinderMass, inferInstance,
    EffectiveSeparation.cylinderMass_computableIn,
    EffectiveSeparation.ofReal_cylinderMass_eq, EffectiveSeparation.ae_separating⟩

/-- There is an actual separator Turing reducible to the fifth halting jump. -/
theorem exists_kolmogorovLovelandRandom_not_martinLofRandom_below_fifthJump :
    ∃ X : Cantor, KolmogorovLovelandRandom X ∧ ¬MartinLofRandom X ∧
      Reduces X (OracleJump.zeroJump 5) := by
  obtain ⟨X, hcomp, hKL, hML⟩ :=
    EffectiveBlockSeparation.exists_separator EffectiveConstruction.concreteRun
  exact ⟨X, hKL, hML, hcomp⟩

end Klr
