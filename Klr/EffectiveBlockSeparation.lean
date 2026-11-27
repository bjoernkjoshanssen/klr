module

public import Klr.EffectiveStageRecursion
public import Klr.EffectiveFixedPartitions
public import Klr.EffectiveBlockProduct
public import Klr.EffectiveKLSelection

/-!
# Effective separation from an actual fourth-jump stage run

The stage run supplies disjoint escaping affine blocks, exact finite codes,
all required probabilistic estimates, and the short ordinary programs used
by the fixed Martin-Löf test. Its block-product law has exact rational
cylinder masses computable in the fourth jump. The one-jump closed-class
selection theorem then produces a separating sequence below the fifth jump.
-/

@[expose] public section

noncomputable section

namespace Klr.EffectiveBlockSeparation

open MeasureTheory _root_.Klr.Computability OracleJump

local instance : Encodable ℚ := (inferInstance : Primcodable ℚ).toEncodable

/-- The complete stage-run interface needed for the effective conclusion. -/
abbrev Run := EffectiveStageRecursion.Run (zeroJump 4)
  UniformStrategyFamily.strategy EffectiveFixedPartitions.high

/-- The actual infinite product law of the selected affine blocks. -/
def law (R : Run) : Measure Cantor := BlockProduct.law R.blocks R.blocks_pairwise

instance (R : Run) : IsProbabilityMeasure (law R) := by
  unfold law
  infer_instance

/-- The exact rational cylinder function obtained by stabilization at the
length of the requested prefix. -/
def cylinderMass (R : Run) : List Bool → ℚ := EffectiveBlockProduct.mass R.output

theorem cylinderMass_computableIn (R : Run) :
    ComputableIn {oracleFunction (zeroJump 4)} (cylinderMass R) :=
  EffectiveBlockProduct.mass_computableIn R.output_computableIn

theorem cylinderMass_eq (R : Run) (s : List Bool) :
    (cylinderMass R s : ℝ) = (law R).real (cylinder s) :=
  EffectiveBlockProduct.mass_eq R.blocks R.blocks_pairwise R.support_escape R.output
    (fun n => (R.description n).2.2.2.2) s

theorem ofReal_cylinderMass_eq (R : Run) (s : List Bool) :
    ENNReal.ofReal (cylinderMass R s : ℝ) = law R (cylinder s) :=
  EffectiveBlockProduct.ofReal_mass_eq R.blocks R.blocks_pairwise R.support_escape R.output
    (fun n => (R.description n).2.2.2.2) s

/-- The stage estimates defeat each normalized simulator; success-preserving
normalization and the effective family's coverage give actual KL randomness. -/
theorem ae_kolmogorovLovelandRandom (R : Run) :
    ∀ᵐ X ∂law R, KolmogorovLovelandRandom X := by
  apply (UniformStrategyFamily.ae_kolmogorovLovelandRandom_iff (law R)).mpr
  intro i
  have hstage := R.stageEstimates EffectiveFixedPartitions.measurableSet_high i
  have hforced := hstage.ae_summable_forcedWager R.blocks_pairwise
  have hfail := BlockRandomness.ae_not_succeeds R.blocks R.blocks_pairwise
    (UniformStrategyFamily.strategy i).normalize
    (UniformStrategyFamily.strategy i).normalize_wager_abs_le_half hforced
  filter_upwards [hfail] with X hX
  exact fun hs => hX ((UniformStrategyFamily.strategy i).normalize_preserves_success hs)

/-- Every finite affine event is closed in the product topology on Cantor space. -/
theorem isClosed_block_event (B : AffineBlock) : IsClosed B.event := by
  change IsClosed ((fun X : Cantor => fun i : B.support => X i.val) ⁻¹'
    {u : B.support → Bool | B.matrix (FiniteMeasure.assignmentEquivF2 u) = B.syndrome})
  exact (isClosed_discrete _).preimage (continuous_pi fun i => continuous_apply i.val)

theorem law_block_event (R : Run) (n : ℕ) : law R (R.blocks n).event = 1 :=
  BlockProduct.law_block_event R.blocks R.blocks_pairwise n

/-- A fourth-jump run yields a KL-random solution to every imposed block
constraint computable from the fifth jump. -/
theorem exists_random_block_solution (R : Run) :
    ∃ X : Cantor, Reduces X (zeroJump 5) ∧ KolmogorovLovelandRandom X ∧
      ∀ n, X ∈ (R.blocks n).event := by
  obtain ⟨X, hX, hklr, hclosed⟩ := EffectiveKLSelection.exists_klr_mem_full_closed
    (law R) (cylinderMass R) (cylinderMass_computableIn R) (cylinderMass_eq R)
    (ae_kolmogorovLovelandRandom R)
  exact ⟨X, hX, hklr, fun n =>
    hclosed (R.blocks n).event (isClosed_block_event _) (law_block_event R n)⟩

/-- All solutions of the selected blocks fail the concrete short-program
Martin-Löf test, independently of the point-selection computation. -/
theorem not_martinLofRandom_of_blocks (R : Run) {X : Cantor}
    (hX : ∀ n, X ∈ (R.blocks n).event) : ¬ MartinLofRandom X := by
  apply AffineDescription.not_martinLofRandom_of_programs
  intro n
  obtain ⟨hrun, hv, _, hshort, hevent⟩ := R.description n
  exact ⟨R.program n, R.output n, hrun, hv, hshort, by rw [hevent]; exact hX n⟩

theorem ae_not_martinLofRandom (R : Run) : ∀ᵐ X ∂law R, ¬ MartinLofRandom X := by
  filter_upwards [BlockProduct.ae_all_blocks R.blocks R.blocks_pairwise] with X hX
  exact not_martinLofRandom_of_blocks R hX

/-- The same fourth-jump-computable measure is concentrated on the full
separating class, not merely on the individual block events. -/
theorem ae_separating (R : Run) :
    ∀ᵐ X ∂law R, KolmogorovLovelandRandom X ∧ ¬ MartinLofRandom X :=
  (ae_kolmogorovLovelandRandom R).and (ae_not_martinLofRandom R)

/-- The desired bounded-degree separator, conditional only on the actual
finite-stage run supplied by the effective construction. -/
theorem exists_separator (R : Run) :
    ∃ X : Cantor, Reduces X (zeroJump 5) ∧
      KolmogorovLovelandRandom X ∧ ¬ MartinLofRandom X := by
  obtain ⟨X, hX, hklr, hblocks⟩ := exists_random_block_solution R
  exact ⟨X, hX, hklr, not_martinLofRandom_of_blocks R hblocks⟩

end Klr.EffectiveBlockSeparation
