module

public import Klr.FiniteStageHistory
public import Klr.StageRecursion
public import Klr.Computability.StageSearch
public import Klr.Computability.RelativeComputable

/-!
# Oracle-computable stage recursion and global gluing

A bounded oracle-computable candidate enumerator need only succeed on valid
finite histories. Its checked outputs preserve that invariant. Iterating the
search therefore produces an actual oracle-computable sequence of finite
candidates. Coherence of the finite histories transfers the four local
estimates to the infinite block sequence and retains its exact short programs.
-/

@[expose] public section

noncomputable section

namespace Klr.EffectiveStageRecursion

open MeasureTheory ProbabilityTheory Encodable
open Klr.Computability FiniteStageCandidate FiniteStageHistory
open scoped ENNReal

local instance : Primcodable Candidate := inferInstance
local instance : Primcodable FiniteStageHistory.History := inferInstance
local instance : Primcodable (Option Candidate) := inferInstance

/-- The semantic output specification of the bounded finite-stage enumerator. -/
def Extension (s : ℕ → BettingStrategy) (H : ℕ → Set Cantor)
    (h : FiniteStageHistory.History) (c : Candidate) : Prop :=
  check h.length (cutoff (fun i => (s i).normalize.scan) h) c = true ∧
    StageRecursion.Step s H (FiniteStageHistory.blocks h) h.length
      (cutoff (fun i => (s i).normalize.scan) h) (StageErrorBudget.rational h.length)
      (FiniteStageCandidate.block c) (horizon c)

/-- A numerical oracle run retaining its finite histories and successful steps. -/
structure Run (A : Oracle) (s : ℕ → BettingStrategy) (H : ℕ → Set Cantor) where
  histories : ℕ → FiniteStageHistory.History
  computable_histories : ComputableIn {oracleFunction A} histories
  zero : histories 0 = []
  valid : ∀ n, FiniteStageHistory.Valid (histories n)
  advance : ∀ n, ∃ c : Candidate,
    histories (n + 1) = histories n ++ [c] ∧ Extension s H (histories n) c

private def nextCode (E : FiniteStageHistory.History → ℕ → Option Candidate)
    (v t : ℕ) : Option ℕ :=
  (E (RelativeComputable.decodeDefault v) t).map fun c =>
    encode ((RelativeComputable.decodeDefault v : FiniteStageHistory.History) ++ [c])

private theorem nextCode_computableIn {A : Oracle}
    {E : FiniteStageHistory.History → ℕ → Option Candidate}
    (hE : ComputableIn₂ {oracleFunction A} E) :
    ComputableIn₂ {oracleFunction A} (nextCode E) := by
  have hread : Primrec (fun p : ℕ × ℕ =>
      (RelativeComputable.decodeDefault p.1 : FiniteStageHistory.History)) :=
    RelativeComputable.primrec_decodeDefault.comp Primrec.fst
  have he := RelativeComputable.comp₂ hE hread.computableIn ComputableIn.snd
  have hmap : Primrec (fun p : FiniteStageHistory.History × Option Candidate =>
      p.2.map fun c => encode (p.1 ++ [c])) :=
    Primrec.option_map Primrec.snd
      (Primrec.encode.comp (Primrec.list_append.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.list_cons.comp Primrec.snd (Primrec.const [])))).to₂
  exact RelativeComputable.comp hmap.computableIn (RelativeComputable.pair hread.computableIn he)

/-- Complete sound bounded search on valid histories gives a run in the same
oracle. No decidability or oracle computation of the semantic invariant is assumed. -/
theorem exists_run {A : Oracle} (s : ℕ → BettingStrategy) (H : ℕ → Set Cantor)
    {E : FiniteStageHistory.History → ℕ → Option Candidate}
    (hE : ComputableIn₂ {oracleFunction A} E)
    (hcomplete : ∀ h, FiniteStageHistory.Valid h → ∃ t c, c ∈ E h t)
    (hsound : ∀ h, FiniteStageHistory.Valid h → ∀ t c, c ∈ E h t → Extension s H h c) :
    Nonempty (Run A s H) := by
  have he := RelativeComputable.encode_recursive
    (RelativeComputable.comp (nextCode_computableIn hE) Primrec.unpair.computableIn)
  let V : ℕ → Prop := fun v => FiniteStageHistory.Valid
    (RelativeComputable.decodeDefault v)
  let T : ℕ → ℕ → Prop := fun v w => ∃ c : Candidate,
    (RelativeComputable.decodeDefault w : FiniteStageHistory.History) =
      RelativeComputable.decodeDefault v ++ [c] ∧
      Extension s H (RelativeComputable.decodeDefault v) c
  have hzero : V (encode ([] : FiniteStageHistory.History)) := by
    simpa only [V, RelativeComputable.decodeDefault_encode] using valid_empty
  have htotal : ∀ v, V v → ∃ t w, w ∈ nextCode E v t := by
    intro v hv
    obtain ⟨t, c, hc⟩ := hcomplete (RelativeComputable.decodeDefault v) hv
    exact ⟨t, _, Option.mem_map.mpr ⟨c, hc, rfl⟩⟩
  have hgood : ∀ v t w, V v → w ∈ nextCode E v t → V w ∧ T v w := by
    intro v t w hv hw
    obtain ⟨c, hc, rfl⟩ := Option.mem_map.mp hw
    have hs := hsound (RelativeComputable.decodeDefault v) hv t c hc
    simp only [V, T, RelativeComputable.decodeDefault_encode]
    exact ⟨hv.append (fun i => (s i).normalize.scan) hs.1, c, rfl, hs⟩
  obtain ⟨r, hr, hr0, hrv, hrs⟩ := exists_computable_stage_run he hzero htotal hgood
  let hist : ℕ → FiniteStageHistory.History := fun n => RelativeComputable.decodeDefault (r n)
  have hhist : ComputableIn {oracleFunction A} hist :=
    RelativeComputable.comp RelativeComputable.primrec_decodeDefault.computableIn
      (RecursiveIn.iff_nat.mpr hr)
  refine ⟨⟨hist, hhist, ?_, hrv, hrs⟩⟩
  simp only [hist, hr0, RelativeComputable.decodeDefault_encode]

namespace Run

variable {A : Oracle} {s : ℕ → BettingStrategy} {H : ℕ → Set Cantor} (R : Run A s H)

theorem length (n : ℕ) : (R.histories n).length = n := by
  induction n with
  | zero => rw [R.zero]; rfl
  | succ n ih =>
    obtain ⟨c, hc, _⟩ := R.advance n
    rw [hc, List.length_append, List.length_singleton, ih]

/-- The actual finite candidate selected at each stage, read from the next history. -/
def candidate (n : ℕ) : Candidate := (R.histories (n + 1)).getD n default

theorem candidate_computableIn : ComputableIn {oracleFunction A} R.candidate := by
  have hh := RelativeComputable.comp R.computable_histories Primrec.succ.computableIn
  have hget : ComputableIn₂ {oracleFunction A}
      (fun l : FiniteStageHistory.History => fun n => l.getD n (default : Candidate)) :=
    (Primrec.list_getD (default : Candidate)).computableIn₂
  have hc := RelativeComputable.comp₂ hget hh (ComputableIn.id (α := ℕ))
  exact RelativeComputable.of_eq hc (fun _ => rfl)

theorem candidate_spec (n : ℕ) :
    R.histories (n + 1) = R.histories n ++ [R.candidate n] ∧
      Extension s H (R.histories n) (R.candidate n) := by
  obtain ⟨c, hc, hs⟩ := R.advance n
  have he : R.candidate n = c := by
    have hd : (R.histories n ++ [c]).getD (R.histories n).length default = c := by simp
    simpa only [candidate, hc, R.length] using hd
  rw [he]
  exact ⟨hc, hs⟩

theorem checked (n : ℕ) :
    Checked n (cutoff (fun i => (s i).normalize.scan) (R.histories n)) (R.candidate n) := by
  have h := check_sound (R.candidate_spec n).2.1
  simpa only [R.length] using h

def blocks (n : ℕ) : AffineBlock := FiniteStageCandidate.block (R.candidate n)
def horizons (n : ℕ) : ℕ := horizon (R.candidate n)
def output (n : ℕ) : AffineCode.Data := FiniteStageCandidate.output (R.candidate n)
def program (n : ℕ) : List Bool := FiniteStageCandidate.program (R.candidate n)

theorem selected_step (n : ℕ) :
    StageRecursion.Step s H (FiniteStageHistory.blocks (R.histories n)) n
      (cutoff (fun i => (s i).normalize.scan) (R.histories n)) (StageErrorBudget.rational n)
      (R.blocks n) (R.horizons n) := by
  simpa only [R.length, blocks, horizons] using (R.candidate_spec n).2.2

theorem output_computableIn : ComputableIn {oracleFunction A} R.output := by
  unfold output
  exact RelativeComputable.comp primrec_output.computableIn R.candidate_computableIn

theorem horizons_computableIn : ComputableIn {oracleFunction A} R.horizons := by
  unfold horizons
  exact RelativeComputable.comp primrec_horizon.computableIn R.candidate_computableIn

theorem program_computableIn : ComputableIn {oracleFunction A} R.program := by
  unfold program
  exact RelativeComputable.comp primrec_program.computableIn R.candidate_computableIn

/-- Every earlier decoded history block is the corresponding final block. -/
theorem histories_blocks_eq (n j : ℕ) (hj : j < n) :
    FiniteStageHistory.blocks (R.histories n) j = R.blocks j := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [(R.candidate_spec n).1, FiniteStageHistory.blocks_append, R.length]
    by_cases hjn : j = n
    · subst j
      exact Function.update_self _ _ _
    · rw [Function.update_of_ne hjn]
      exact ih (by omega)

theorem histories_horizons_eq (n j : ℕ) (hj : j < n) :
    FiniteStageHistory.horizons (R.histories n) j = R.horizons j := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [(R.candidate_spec n).1, FiniteStageHistory.horizons_append, R.length]
    by_cases hjn : j = n
    · subst j
      exact Function.update_self _ _ _
    · rw [Function.update_of_ne hjn]
      exact ih (by omega)

theorem histories_law_eq (n a : ℕ) (ha : a ≤ n) :
    PrefixStage.law (FiniteStageHistory.blocks (R.histories n)) a =
      PrefixStage.law R.blocks a := by
  apply congrArg AffineBlock.finiteStageLaw
  funext j
  exact R.histories_blocks_eq n j.val (lt_of_lt_of_le j.isLt ha)

theorem blocks_pairwise : Pairwise (fun i j => Disjoint (R.blocks i).support
    (R.blocks j).support) := by
  intro i j hij
  have hi : i < max i j + 1 := Nat.lt_succ_of_le (le_max_left _ _)
  have hj : j < max i j + 1 := Nat.lt_succ_of_le (le_max_right _ _)
  have h := (R.valid (max i j + 1)).disjoint hij
  dsimp only at h
  rwa [R.histories_blocks_eq _ i hi, R.histories_blocks_eq _ j hj] at h

/-- Stage indices themselves are eventually below every new support coordinate. -/
theorem support_escape (n q : ℕ) (hq : q ∈ (R.blocks n).support) : n ≤ q := by
  have h := length_lt_cutoff (fun i => (s i).normalize.scan) (R.histories n)
  rw [R.length] at h
  exact h.le.trans ((R.selected_step n).above q hq)

/-- Future blocks avoid every branch through each earlier protected horizon. -/
theorem horizon_avoidance (i j k : ℕ) (hij : i ≤ j) (hjk : j < k)
    (v : List Bool) (hv : v.length = R.horizons j) :
    (R.blocks k).UnreadFullRank (s i).normalize.scan v := by
  apply HorizonAvoidance.unreadFullRank_of_queryBound_le _ _ (R.horizons j) _ v hv.le
  intro q hq
  have hb := FiniteStageHistory.queryBound_le_cutoff
    (fun i => (s i).normalize.scan) (R.histories k)
    (show j < (R.histories k).length by simpa only [R.length] using hjk) i hij
  rw [R.histories_horizons_eq k j hjk] at hb
  exact hb.trans ((R.selected_step k).above q hq)

/-- The four actual stage estimates hold for each eventually protected strategy. -/
theorem stageEstimates (hH : ∀ i, MeasurableSet (H i)) (i : ℕ) :
    StageEstimates R.blocks (s i).normalize.scan (s i).normalize.capital.wager
      R.horizons (H i) i := by
  refine ⟨hH i, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hij v hv k hjk
    exact R.horizon_avoidance i j k hij hjk v hv
  · intro j hij
    have h := (R.selected_step j).early_and_partial i hij
    rw [R.histories_law_eq j j le_rfl,
      ← PrefixStage.law_succ_eq_cond, StageRecursion.earlyWager_single] at h
    have hb : ENNReal.ofReal (4 * (StageErrorBudget.rational j : ℝ)) =
        4 * StageErrorBudget.error j := by
      simpa only [Nat.cast_ofNat] using StageErrorBudget.ofReal_mul_rational 4 j
    rwa [hb] at h
  · intro j hij
    have h := (R.selected_step j).first_drop_tail i hij
    rw [R.histories_law_eq j j le_rfl, ← PrefixStage.law_succ_eq_cond] at h
    have hb : ENNReal.ofReal (2 * (StageErrorBudget.rational j : ℝ)) =
        2 * StageErrorBudget.error j := by
      simpa only [Nat.cast_ofNat] using StageErrorBudget.ofReal_mul_rational 2 j
    rwa [hb] at h
  · intro j hij
    have h := (R.selected_step j).high_no_drop i hij
    rwa [R.histories_law_eq j j le_rfl, StageErrorBudget.ofReal_rational] at h
  · intro j hij k hjk
    have h := (R.selected_step k).earlier_low_drop (j + 1) (by omega) i (by omega)
    rwa [R.histories_law_eq k (j + 1) (by omega), StageErrorBudget.ofReal_rational] at h

/-- The actual computable output and program families supply every test-level description. -/
theorem description (n : ℕ) :
    R.output n ∈ AffineDescription.run (R.program n) ∧
      AffineCode.valid (R.output n) = true ∧ AffineCode.rank (R.output n) = (R.blocks n).rank ∧
      2 * (R.program n).length + n + 1 ≤ AffineCode.rank (R.output n) ∧
      AffineCode.event (R.output n) = (R.blocks n).event :=
  ⟨(R.checked n).runs, (R.checked n).output_valid, (R.checked n).rank,
    (R.checked n).budget, (R.checked n).event⟩

end Run

end Klr.EffectiveStageRecursion
