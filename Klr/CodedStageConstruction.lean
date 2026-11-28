module

public import Klr.FiniteStageCandidate
public import Klr.StageOneStep

/-!
# Completeness of finite candidate search for the stage construction

The mathematical preparation and the exact finite representation retained by
its result produce a candidate passing the ordinary syntactic checker.
Every positive rational error is allowed, so a later oracle search can use
strict slack in its probability tests. The stronger finite objective bound
is retained for any finite code header representing the old conditional law.
-/

@[expose] public section

namespace Klr.CodedStageConstruction

open MeasureTheory ProbabilityTheory
open StagePrepared FiniteStageCandidate

/-- The rational objective of a valid finite block is the actual integral
under the old law conditioned on that very block. -/
theorem cost_eq_integral (rules : List BettingStrategy) (cs : List AffineCode.Data)
    {d : FiniteStageData.BlockData} (hd : FiniteStageData.valid d = true) (V : ℕ) :
    (StageSyndromeObjective.cost rules cs (FiniteStageData.pool d)
      (FiniteStageData.entry d) V (FiniteStageData.syndrome d) : ℝ) =
      ∫ X, StageHorizonChoice.objective (FiniteStageData.block d)
        (fun i : Fin rules.length => (rules.get i).normalize.scan)
        (fun i : Fin rules.length => StageFiniteWager.normalizedWager (rules.get i)) V X
        ∂cond (StageFiniteProbability.law cs) (FiniteStageData.block d).event := by
  rw [FiniteStageData.block_of_valid d hd]
  exact StageSyndromeObjective.cost_eq_integral rules cs (FiniteStageData.pool d)
    ((FiniteStageData.valid_eq_true d).mp hd).1 (FiniteStageData.entry d)
    ((FiniteStageData.valid_eq_true d).mp hd).2 V (FiniteStageData.syndrome d)
    (SparseSearch.wordVector (FiniteStageData.rank d) (FiniteStageData.syndrome d))

/-- The finite rational cost used by the future bounded stage checker. -/
noncomputable def cost (rules : List BettingStrategy) (cs : List AffineCode.Data)
    (c : Candidate) : ℚ :=
  StageSyndromeObjective.cost rules cs (FiniteStageData.pool (data c))
    (FiniteStageData.entry (data c)) (horizon c) (FiniteStageData.syndrome (data c))

theorem computable_cost (rules : List BettingStrategy) :
    Computable₂ (cost rules) := by
  have hd := primrec_data.to_comp.comp (Computable.snd :
    Computable (fun p : List AffineCode.Data × Candidate => p.2))
  exact StageSyndromeObjective.computable_cost rules Computable.fst
    (FiniteStageData.primrec_pool.to_comp.comp hd) (FiniteStageData.primrec_entry.to_comp.comp hd)
    (primrec_horizon.to_comp.comp Computable.snd) (FiniteStageData.primrec_syndrome.to_comp.comp hd)

/-- A represented stage result supplies a genuinely finite checked candidate,
with the exact same block and horizon and the stronger objective estimate. -/
theorem result_has_candidate {s : ℕ → BettingStrategy} {H : ℕ → Set Cantor}
    {old : ℕ → AffineBlock} {n z : ℕ} {error : ℚ} {r : ℕ} {G : List ℕ}
    (R : StageOneStep.Result old n (protectedRules s n) (fun i => H i) error r n G)
    (hG : ∀ p ∈ G, z ≤ p) :
    ∃ c : Candidate, check n z c = true ∧ block c = R.block ∧ horizon c = R.horizon ∧
      ∀ cs : List AffineCode.Data, StageFiniteProbability.law cs = PrefixStage.law old n →
        (cost (protectedRules s n) cs c : ℝ) < 4 * (error : ℝ) := by
  obtain ⟨d, hd, heq, hpool⟩ := R.represented
  have habove : ∀ p ∈ FiniteStageData.pool d, z ≤ p := by rwa [hpool]
  have hr : AffineCode.rank R.code = (FiniteStageData.block d).rank := by
    rw [heq]
    exact R.code_rank.trans R.block_rank.symm
  have he : AffineCode.event R.code = (FiniteStageData.block d).event :=
    R.event_eq.trans (congrArg AffineBlock.event heq.symm)
  have hb : 2 * R.program.length + n + 1 ≤ AffineCode.rank R.code := by
    rw [R.code_rank]
    exact R.budget
  obtain ⟨t, ht⟩ := check_complete (V := R.horizon) hd habove R.valid hr he hb R.runs
  refine ⟨(d, R.horizon, R.program, R.code, t), ht, heq, rfl, ?_⟩
  intro cs hcs
  change (StageSyndromeObjective.cost (protectedRules s n) cs (FiniteStageData.pool d)
    (FiniteStageData.entry d) R.horizon (FiniteStageData.syndrome d) : ℝ) < _
  rw [cost_eq_integral _ _ hd _, heq, hcs]
  exact R.finite_cost

/-- A prescribed fixed partition with the ordinary pool property supplies a
successful finite candidate after every disjoint history and at every positive
rational error. No oracle effectiveness is assumed in this existence proof. -/
theorem exists_coded_step_of_pools (s : ℕ → BettingStrategy)
    (H : ℕ → Set Cantor) (hH : ∀ i, MeasurableSet (H i))
    (hpool : PoolConstruction.ComputablePools (fun i => (s i).normalize.scan) H)
    (old : ℕ → AffineBlock)
    (hold : Pairwise (fun i j => Disjoint (old i).support (old j).support))
    (n z : ℕ) (error : ℚ) (he : 0 < error) :
    ∃ c : Candidate, check n z c = true ∧
      StageRecursion.Step s H old n z error (block c) (horizon c) ∧
      ∀ cs : List AffineCode.Data, StageFiniteProbability.law cs = PrefixStage.law old n →
        (cost (protectedRules s n) cs c : ℝ) < 4 * (error : ℝ) := by
  let z' := max z ((PrefixStage.prefixSupport old n).sup id + 1)
  have hz : ∀ k < n, ∀ p ∈ (old k).support, p < z' := by
    intro k hk p hp
    have hmem : p ∈ PrefixStage.prefixSupport old n :=
      (PrefixStage.mem_prefixSupport old n p).mpr ⟨k, hk, hp⟩
    exact (Nat.lt_succ_of_le (Finset.le_sup (f := id) hmem)).trans_le (le_max_right _ _)
  obtain ⟨P⟩ := StagePrepared.prepared_of_pools s H hH hpool old hold n z' error he
  obtain ⟨R⟩ := StageOneStep.result_of_prepared s H old hold n z' he P hz
  have hG : ∀ p ∈ P.pool, z ≤ p := by
    intro p hp
    exact (le_max_left z _).trans (P.goodPool.2.2.1 p hp)
  obtain ⟨c, hc, hblock, hV, hcost⟩ := result_has_candidate R hG
  refine ⟨c, hc, ?_, hcost⟩
  rw [hblock, hV]
  exact R.to_step hG

end Klr.CodedStageConstruction
