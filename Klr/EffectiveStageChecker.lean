module

public import Klr.StageProbabilityRequests
public import Klr.UniformStageCost
public import Klr.StageCostSoundness

/-!
# A genuine fourth-jump checker for finite stage extensions

The checker combines ordinary execution and affine-code verification, the
exact rational finite objective, and finite rational certificates for every
strict probability bound. Mathematical existence at half the requested
error supplies the strict slack needed for completeness. Malformed histories
need not have a successful extension; the checker itself is total on all data.
-/

@[expose] public section

noncomputable section

namespace Klr.EffectiveStageChecker

open MeasureTheory ProbabilityTheory FiniteStageCandidate FiniteStageHistory
open _root_.Klr.Computability

local instance : Encodable ℚ := (inferInstance : Primcodable ℚ).toEncodable
local instance : Primcodable Candidate := inferInstance
local instance : Primcodable History := inferInstance
local instance : Primcodable (Option Candidate) := inferInstance

def cost (h : History) (c : Candidate) : ℚ :=
  CodedStageConstruction.cost
    (StagePrepared.protectedRules UniformStrategyFamily.strategy h.length) (codes h) c

theorem cost_computable : ComputableIn₂ {oracleFunction (OracleJump.zeroJump 4)} cost := by
  have ha : Primrec (fun p : History × Candidate => (p.1.length, (codes p.1, p.2))) :=
    (Primrec.list_length.comp Primrec.fst).pair
      ((primrec_codes.comp Primrec.fst).pair Primrec.snd)
  exact RelativeComputable.comp
    (f := fun p : ℕ × (List AffineCode.Data × Candidate) =>
      CodedStageConstruction.cost
        (StagePrepared.protectedRules UniformStrategyFamily.strategy p.1) p.2.1 p.2.2)
    (g := fun p : History × Candidate => (p.1.length, (codes p.1, p.2)))
    UniformStageCost.cost_computableIn_fourth ha.computableIn

/-- Every test is finite once the oracle has computed the rational approximations. -/
def accepted (h : History) (c : Candidate) (k : ℕ) : Bool :=
  check h.length (cutoff EffectiveStageProbability.scans h) c &&
    (decide (cost h c < 4 * StageErrorBudget.rational h.length) &&
      EffectiveStageProbability.probabilityName.certificates
        (StageProbabilityRequests.requests h c) k)

theorem accepted_computable : ComputableIn {oracleFunction (OracleJump.zeroJump 4)}
    (fun p : (History × Candidate) × ℕ => accepted p.1.1 p.1.2 p.2) := by
  have hhist : Primrec (fun p : (History × Candidate) × ℕ => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hcand : Primrec (fun p : (History × Candidate) × ℕ => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hz :=
    (computable_cutoff EffectiveStageProbability.scans
      EffectiveStageProbability.computable_query).comp hhist.to_comp
  have hargs : Computable (fun p : (History × Candidate) × ℕ =>
      ((p.1.1.length, cutoff EffectiveStageProbability.scans p.1.1), p.1.2)) :=
    (((Primrec.list_length.comp hhist).to_comp.pair hz).pair hcand.to_comp)
  have hf := computable_check.comp hargs
  have hcost : ComputableIn {oracleFunction (OracleJump.zeroJump 4)}
      (fun p : (History × Candidate) × ℕ => cost p.1.1 p.1.2) :=
    RelativeComputable.comp (f := fun p : History × Candidate => cost p.1 p.2)
      (g := fun p : (History × Candidate) × ℕ => p.1) cost_computable ComputableIn.fst
  have hb : Primrec (fun p : (History × Candidate) × ℕ =>
      4 * StageErrorBudget.rational p.1.1.length) :=
    RationalComputability.primrec_rat_mul.comp (Primrec.const 4)
      (StageProbabilityRequests.primrec_error.comp (Primrec.list_length.comp hhist))
  have hlt := RelativeComputable.comp₂ (f := fun q r : ℚ => decide (q < r))
    PoolAdvice.computable_rat_lt.computableIn hcost hb.computableIn
  have hr : Primrec (fun p : (History × Candidate) × ℕ =>
      StageProbabilityRequests.requests p.1.1 p.1.2) :=
    Primrec.comp (f := fun p : History × Candidate => StageProbabilityRequests.requests p.1 p.2)
      StageProbabilityRequests.primrec_requests Primrec.fst
  have hcert := RelativeComputable.comp₂
    (f := EffectiveStageProbability.probabilityName.certificates)
    EffectiveStageProbability.probabilityName.certificates_computable
    hr.computableIn ComputableIn.snd
  have hfinal := RelativeComputable.comp₂ (f := fun b d : Bool => b && d)
    Primrec.and.computableIn₂
    hf.computableIn
    (RelativeComputable.comp₂ (f := fun b d : Bool => b && d) Primrec.and.computableIn₂ hlt hcert)
  exact RelativeComputable.of_eq hfinal (fun _ => rfl)

theorem accepted_eq_true (h : History) (c : Candidate) (k : ℕ) :
    accepted h c k = true ↔
      check h.length (cutoff EffectiveStageProbability.scans h) c = true ∧
      cost h c < 4 * StageErrorBudget.rational h.length ∧
      EffectiveStageProbability.probabilityName.certificates
        (StageProbabilityRequests.requests h c) k = true := by
  simp only [accepted, Bool.and_eq_true, decide_eq_true_eq]

/-- The new exact code header is the old law conditioned on the checked block. -/
theorem law_new_header {h : History} (hh : Valid h) {c : Candidate} {n z : ℕ}
    (hc : check n z c = true) :
    StageFiniteProbability.law (output c :: codes h) =
      cond (PrefixStage.law (blocks h) h.length) (FiniteStageCandidate.block c).event := by
  have hs := check_sound hc
  rw [← law_codes hh, StageFiniteProbability.law, StageFiniteProbability.law,
    StageFiniteProbability.event_cons, hs.event, Set.inter_comm,
    cond_cond_eq_cond_inter (StageFiniteProbability.measurableSet_event _)
      (FiniteStageCandidate.block c).measurableSet_event]

/-- Successful rational certificates imply the original semantic stage relation. -/
theorem accepted_sound {h : History} (hh : Valid h) {c : Candidate} {k : ℕ}
    (hc : accepted h c k = true) :
    check h.length (cutoff EffectiveStageProbability.scans h) c = true ∧
      StageRecursion.Step UniformStrategyFamily.strategy EffectiveFixedPartitions.high
        (blocks h) h.length (cutoff EffectiveStageProbability.scans h)
        (StageErrorBudget.rational h.length) (FiniteStageCandidate.block c) (horizon c) := by
  obtain ⟨hcheck, hcost, hcert⟩ := (accepted_eq_true h c k).mp hc
  have hrequests := (EffectiveStageProbability.probabilityName.exists_certificates_iff
    (StageProbabilityRequests.requests h c)).mp ⟨k, hcert⟩
  obtain ⟨htail, hhigh, hlow⟩ :=
    (StageProbabilityRequests.all_holds_iff h c).mp hrequests
  refine ⟨hcheck, StageCostSoundness.step_of_cost_and_bounds
    UniformStrategyFamily.strategy EffectiveFixedPartitions.high (blocks h) hh.disjoint
    h.length (cutoff EffectiveStageProbability.scans h) (StageErrorBudget.rational h.length)
    c hcheck (codes h) (law_codes hh) ?_ ?_ ?_ ?_⟩
  · have he := (Rat.cast_lt (K := ℝ)).mpr hcost
    simpa only [cost, Rat.cast_mul, Rat.cast_ofNat] using he.le
  · intro i hi
    have ht := (htail i hi).le
    simpa only [EffectiveStageProbability.probability_tail, law_new_header hh hcheck,
      EffectiveStageProbability.scans, FiniteStageCandidate.block,
      Rat.cast_mul, Rat.cast_ofNat] using ht
  · intro i hi
    have ht := (hhigh i hi).le
    simpa only [EffectiveStageProbability.probability_high, law_codes hh,
      EffectiveStageProbability.highEvent, EffectiveStageProbability.scans,
      FiniteStageCandidate.block] using ht
  · intro a ha i hi
    have ht := (hlow a ha i hi).le
    simpa only [EffectiveStageProbability.probability_low, law_codes_take hh a ha,
      EffectiveStageProbability.lowEvent, EffectiveStageProbability.scans,
      FiniteStageCandidate.block] using ht

private theorem real_lt_of_measure_le (μ : Measure Cantor) (S : Set Cantor)
    {r t : ℝ} (hr : 0 ≤ r) (h : μ S ≤ ENNReal.ofReal r) (hrt : r < t) :
    μ.real S < t := by
  have he := ENNReal.toReal_mono (by simp : ENNReal.ofReal r ≠ ⊤) h
  rw [ENNReal.toReal_ofReal hr] at he
  exact he.trans_lt hrt

/-- Half-budget existence ensures that all finitely many strict certificates
eventually succeed at a common precision. -/
theorem exists_accepted (h : History) (hh : Valid h) :
    ∃ c k, accepted h c k = true := by
  let ε := StageErrorBudget.rational h.length
  have hε : (0 : ℝ) < ε := StageErrorBudget.rational_cast_pos h.length
  have hhalf : (0 : ℚ) < ε / 2 :=
    div_pos (StageErrorBudget.rational_pos h.length) (by norm_num)
  obtain ⟨c, hc, hstep, hcost⟩ := CodedStageConstruction.exists_coded_step_of_pools
    UniformStrategyFamily.strategy EffectiveFixedPartitions.high
    EffectiveFixedPartitions.measurableSet_high EffectiveFixedPartitions.computable_pools
    (blocks h) hh.disjoint h.length (cutoff EffectiveStageProbability.scans h) (ε / 2) hhalf
  have hcost' : cost h c < 4 * ε := by
    have he := hcost (codes h) (law_codes hh)
    apply (Rat.cast_lt (K := ℝ)).mp
    change (cost h c : ℝ) < ((4 * ε : ℚ) : ℝ)
    dsimp only [cost] at *
    push_cast at he ⊢
    linarith
  have hrequests : ∀ r ∈ StageProbabilityRequests.requests h c,
      EffectiveRealApproximation.Holds EffectiveStageProbability.probability r := by
    apply (StageProbabilityRequests.all_holds_iff h c).mpr
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      have ht := real_lt_of_measure_le _ _ (by positivity)
        (hstep.first_drop_tail i hi) (show 2 * ((ε / 2 : ℚ) : ℝ) < ((2 * ε : ℚ) : ℝ) by
          push_cast; linarith)
      simpa only [EffectiveStageProbability.probability_tail, law_new_header hh hc,
        EffectiveStageProbability.scans, FiniteStageCandidate.block] using ht
    · intro i hi
      have ht := real_lt_of_measure_le _ _ (by positivity)
        (hstep.high_no_drop i hi) (show ((ε / 2 : ℚ) : ℝ) < (ε : ℝ) by
          push_cast; linarith)
      simpa only [EffectiveStageProbability.probability_high, law_codes hh,
        EffectiveStageProbability.highEvent, EffectiveStageProbability.scans,
        FiniteStageCandidate.block] using ht
    · intro a ha i hi
      have ht := real_lt_of_measure_le _ _ (by positivity)
        (hstep.earlier_low_drop a ha i hi) (show ((ε / 2 : ℚ) : ℝ) < (ε : ℝ) by
          push_cast; linarith)
      simpa only [EffectiveStageProbability.probability_low, law_codes_take hh a ha,
        EffectiveStageProbability.lowEvent, EffectiveStageProbability.scans,
        FiniteStageCandidate.block] using ht
  obtain ⟨k, hk⟩ := (EffectiveStageProbability.probabilityName.exists_certificates_iff
    (StageProbabilityRequests.requests h c)).mpr hrequests
  exact ⟨c, k, (accepted_eq_true h c k).mpr ⟨hc, hcost', hk⟩⟩

/-- A numerical search parameter encodes both the candidate and its precision. -/
def searchStep (h : History) (t : ℕ) : Option Candidate :=
  let p : Candidate × ℕ := RelativeComputable.decodeDefault t
  if accepted h p.1 p.2 then some p.1 else none

theorem searchStep_computable :
    ComputableIn₂ {oracleFunction (OracleJump.zeroJump 4)} searchStep := by
  have hd : Primrec (fun p : History × ℕ =>
      RelativeComputable.decodeDefault (α := Candidate × ℕ) p.2) :=
    RelativeComputable.primrec_decodeDefault.comp Primrec.snd
  have ha : Primrec (fun p : History × ℕ =>
      ((p.1, (RelativeComputable.decodeDefault (α := Candidate × ℕ) p.2).1),
        (RelativeComputable.decodeDefault (α := Candidate × ℕ) p.2).2)) :=
    (Primrec.fst.pair (Primrec.fst.comp hd)).pair (Primrec.snd.comp hd)
  have hb := RelativeComputable.comp
    (f := fun p : (History × Candidate) × ℕ => accepted p.1.1 p.1.2 p.2)
    (g := fun p : History × ℕ =>
      ((p.1, (RelativeComputable.decodeDefault (α := Candidate × ℕ) p.2).1),
        (RelativeComputable.decodeDefault (α := Candidate × ℕ) p.2).2))
    accepted_computable ha.computableIn
  have hs : Primrec (fun p : History × ℕ =>
      some (RelativeComputable.decodeDefault (α := Candidate × ℕ) p.2).1) :=
    Primrec.option_some.comp (Primrec.fst.comp hd)
  have he := UniformStageCost.computableIn_cond hb hs.computableIn
    (ComputableIn.const (none : Option Candidate))
  exact RelativeComputable.of_eq he fun _ => by simp only [searchStep, Bool.cond_eq_ite]

theorem searchStep_complete (h : History) (hh : Valid h) :
    ∃ t c, c ∈ searchStep h t := by
  obtain ⟨c, k, hck⟩ := exists_accepted h hh
  refine ⟨Encodable.encode (c, k), c, ?_⟩
  simp only [searchStep, RelativeComputable.decodeDefault_encode, hck, ite_true,
    Option.mem_some_iff]

theorem searchStep_sound {h : History} (hh : Valid h) {t : ℕ} {c : Candidate}
    (hc : c ∈ searchStep h t) :
    check h.length (cutoff EffectiveStageProbability.scans h) c = true ∧
      StageRecursion.Step UniformStrategyFamily.strategy EffectiveFixedPartitions.high
        (blocks h) h.length (cutoff EffectiveStageProbability.scans h)
        (StageErrorBudget.rational h.length) (FiniteStageCandidate.block c) (horizon c) := by
  dsimp only [searchStep] at hc
  split_ifs at hc with ha
  · have he := Option.mem_some_iff.mp hc
    subst c
    exact accepted_sound hh ha
  · simp at hc

end Klr.EffectiveStageChecker
