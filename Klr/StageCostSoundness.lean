module

public import Klr.CodedStageConstruction

/-!
# Soundness of finite objective and probability certificates

The executable rational support-wager objective dominates every early-wager
estimate. Together with the three real probability bounds and the ordinary
finite candidate checker, it proves the original semantic stage relation.
-/

@[expose] public section

namespace Klr.StageCostSoundness

open MeasureTheory ProbabilityTheory StagePrepared FiniteStageCandidate
open scoped BigOperators

theorem step_of_cost_and_bounds (s : ℕ → BettingStrategy) (H : ℕ → Set Cantor)
    (old : ℕ → AffineBlock)
    (hold : Pairwise (fun i j => Disjoint (old i).support (old j).support))
    (n z : ℕ) (error : ℚ) (c : Candidate)
    (hcheck : check n z c = true) (cs : List AffineCode.Data)
    (hcs : StageFiniteProbability.law cs = PrefixStage.law old n)
    (hcost : (CodedStageConstruction.cost (protectedRules s n) cs c : ℝ) ≤ 4 * (error : ℝ))
    (htail : ∀ i ≤ n, (cond (PrefixStage.law old n) (block c).event).real
      (StoppingTranscript.rankDropTailEvent (block c) (s i).normalize.scan (horizon c)) ≤
        2 * (error : ℝ))
    (hhigh : ∀ i ≤ n, (PrefixStage.law old n).real
      ((s i).normalize.scan.observationMap ⁻¹' H i ∩
        NoDrop.noDropEvent (block c) (s i).normalize.scan) ≤ (error : ℝ))
    (hlow : ∀ a ≤ n, ∀ i ≤ n, (PrefixStage.law old a).real
      ((s i).normalize.scan.observationMap ⁻¹' (H i)ᶜ ∩
        LateDropBound.hasDrop (block c) (s i).normalize.scan) ≤ (error : ℝ)) :
    StageRecursion.Step s H old n z error (block c) (horizon c) := by
  have hc := check_sound hcheck
  let rules := protectedRules s n
  let μ := cond (PrefixStage.law old n) (block c).event
  let π : Fin rules.length → ScanRule := fun i => (rules.get i).normalize.scan
  let w : Fin rules.length → List Bool → ℚ :=
    fun i => StageFiniteWager.normalizedWager (rules.get i)
  let : IsProbabilityMeasure (PrefixStage.law old n) :=
    PrefixStage.law_isProbabilityMeasure old hold n
  have hh : ∀ i v, |(w i v : ℝ)| ≤ (1 / 2 : ℝ) :=
    fun i v => StageFiniteWager.normalizedWager_abs_le_half (rules.get i) v
  have hobj : (∫ X, StageHorizonChoice.objective (block c) π w (horizon c) X ∂μ) ≤
      4 * (error : ℝ) := by
    have he := CodedStageConstruction.cost_eq_integral rules cs hc.valid (horizon c)
    rw [hcs] at he
    exact he ▸ hcost
  have hsum := (StageHorizonChoice.sum_early_partial_le_objective μ (block c) π w
    (horizon c) hh).trans hobj
  refine ⟨hc.above, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    let j : Fin rules.length := ⟨i, by
      simpa only [rules, length_protectedRules] using Nat.lt_succ_of_le hi⟩
    have hj : (∫ X, StageHorizonChoice.earlyWager (block c) (π j) (w j) (horizon c) X ∂μ) +
        μ.real (LateDropBound.partialEvent (block c) (π j) (horizon c)) ≤ 4 * (error : ℝ) := by
      apply le_trans _ hsum
      exact Finset.single_le_sum
        (f := fun k : Fin rules.length =>
          (∫ X, StageHorizonChoice.earlyWager (block c) (π k) (w k) (horizon c) X ∂μ) +
            μ.real (LateDropBound.partialEvent (block c) (π k) (horizon c)))
        (fun k _ => add_nonneg
          (integral_nonneg (StageHorizonChoice.earlyWager_nonneg (block c) (π k) (w k) (horizon c)))
          measureReal_nonneg) (Finset.mem_univ j)
    have he := StageHorizonChoice.early_lintegral_add_measure_le μ (block c) (π j)
      (w j) (horizon c) (hh j) hj
    simpa only [μ, π, w, rules, get_protectedRules, j,
      StageHorizonChoice.earlyWager, StageFiniteWager.cast_normalizedWager] using he
  · intro i hi
    exact StageOneStep.measure_le_of_real_le _ _ (htail i hi)
  · intro i hi
    exact StageOneStep.measure_le_of_real_le _ _ (hhigh i hi)
  · intro a ha i hi
    let : IsProbabilityMeasure (PrefixStage.law old a) :=
      PrefixStage.law_isProbabilityMeasure old hold a
    exact StageOneStep.measure_le_of_real_le _ _ (hlow a ha i hi)
  · exact ⟨program c, output c, hc.runs, hc.output_valid, hc.rank, hc.budget, hc.event⟩

end Klr.StageCostSoundness
