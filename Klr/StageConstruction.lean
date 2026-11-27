module

public import Klr.StageOneStep
public import Klr.StageRecursion

/-!
# The completed stage construction

The Borel partitions are fixed before any stage is chosen. For every finite
history, preparation supplies a candidate and a fixed reconstruction program;
the one-step theorem supplies its actual horizon, syndrome and short output.
Enlarging the requested cutoff separates the new block from every old support.
This discharges the extension premise of the global recursion.
-/

@[expose] public section

noncomputable section

namespace Klr.StageConstruction

open MeasureTheory

/-- A prescribed family of partitions with the ordinary pool contract supports
every finite stage, at any positive rational error. -/
theorem exists_step_of_pools (s : ℕ → BettingStrategy)
    (H : ℕ → Set Cantor) (hH : ∀ i, MeasurableSet (H i))
    (hpool : PoolConstruction.ComputablePools (fun i => (s i).normalize.scan) H)
    (old : ℕ → AffineBlock)
    (hold : Pairwise (fun i j => Disjoint (old i).support (old j).support))
    (n z : ℕ) (error : ℚ) (he : 0 < error) :
    ∃ C V, StageRecursion.Step s H old n z error C V := by
  let z' := max z ((PrefixStage.prefixSupport old n).sup id + 1)
  have hz : ∀ k < n, ∀ p ∈ (old k).support, p < z' := by
    intro k hk p hp
    have hmem : p ∈ PrefixStage.prefixSupport old n :=
      (PrefixStage.mem_prefixSupport old n p).mpr ⟨k, hk, hp⟩
    have hle : p ≤ (PrefixStage.prefixSupport old n).sup id :=
      Finset.le_sup (f := id) hmem
    exact lt_of_lt_of_le (Nat.lt_succ_of_le hle) (le_max_right _ _)
  obtain ⟨P⟩ := StagePrepared.prepared_of_pools s H hH hpool old hold n z' error he
  obtain ⟨C, V, hstep⟩ := P.to_step hold he hz
  refine ⟨C, V, { hstep with above := ?_ }⟩
  intro p hp
  exact (le_max_left z _).trans (hstep.above p hp)

/-- One fixed family of Borel partitions admits an actual, fully represented
extension after every disjoint finite history and beyond every requested cutoff. -/
theorem exists_fixed_partitions_steps (s : ℕ → BettingStrategy) :
    ∃ H : ℕ → Set Cantor, (∀ i, MeasurableSet (H i)) ∧
      ∀ old : ℕ → AffineBlock,
        Pairwise (fun i j => Disjoint (old i).support (old j).support) →
        ∀ n z : ℕ, ∃ C V,
          StageRecursion.Step s H old n z (StageErrorBudget.rational n) C V := by
  obtain ⟨H, hH, hpool⟩ := PoolConstruction.exists_fixed_partitions_computable_pools
    (fun i => (s i).normalize.scan)
  refine ⟨H, hH, ?_⟩
  intro old hold n z
  exact exists_step_of_pools s H hH hpool old hold n z (StageErrorBudget.rational n)
    (StageErrorBudget.rational_pos n)

/-- The actual infinite block sequence has every required estimate and one
short exact affine description at each Martin-Löf test level. -/
theorem exists_sequence (s : ℕ → BettingStrategy) :
    ∃ (H : ℕ → Set Cantor) (B : ℕ → AffineBlock) (V : ℕ → ℕ),
      (∀ i, MeasurableSet (H i)) ∧
      Pairwise (fun i j => Disjoint (B i).support (B j).support) ∧
      (∀ i, StageEstimates B (s i).normalize.scan
        (s i).normalize.capital.wager V (H i) i) ∧
      ∀ n : ℕ, ∃ (p : List Bool) (c : AffineCode.Data),
        c ∈ AffineDescription.run p ∧ AffineCode.valid c = true ∧
          2 * p.length + n + 1 ≤ AffineCode.rank c ∧ AffineCode.event c = (B n).event := by
  obtain ⟨H, hH, hstep⟩ := exists_fixed_partitions_steps s
  obtain ⟨B, V, hdis, hest, hprogram⟩ := StageRecursion.exists_sequence s H hstep hH
  exact ⟨H, B, V, hH, hdis, hest, hprogram⟩

end Klr.StageConstruction
