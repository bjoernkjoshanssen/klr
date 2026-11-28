module

public import Klr.FiniteStageData

/-!
# Executable finite candidates with exact short descriptions

A candidate contains only finite pool/matrix data, a horizon, a binary
program, its affine-code output, and an execution bound. A total computable
checker verifies the execution and compares finite truth tables to certify
that the program describes the exact decoded block. Probability estimates
are deliberately separate from this purely finite checker.
-/

@[expose] public section

namespace Klr.FiniteStageCandidate

open SparseSearch FiniteStageData

local instance : DecidableEq (Option AffineCode.Data) := Option.instDecidableEq

abbrev Candidate := BlockData × ℕ × List Bool × AffineCode.Data × ℕ

def data (c : Candidate) : BlockData := c.1
def horizon (c : Candidate) : ℕ := c.2.1
def program (c : Candidate) : List Bool := c.2.2.1
def output (c : Candidate) : AffineCode.Data := c.2.2.2.1
def time (c : Candidate) : ℕ := c.2.2.2.2

noncomputable def block (c : Candidate) : AffineBlock := FiniteStageData.block (data c)

theorem primrec_data : Primrec data := Primrec.fst
theorem primrec_horizon : Primrec horizon := Primrec.fst.comp Primrec.snd
theorem primrec_program : Primrec program := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
theorem primrec_output : Primrec output :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
theorem primrec_time : Primrec time :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

/-- Actual bounded execution of the ordinary affine-description interpreter. -/
def boundedRun (p : List Bool) (t : ℕ) : Option AffineCode.Data :=
  (Nat.Partrec.Code.evaln t (AffineDescription.programCode p)
    (AffineDescription.programInput p)).map AffineDescription.decodeOutput

theorem computable_boundedRun : Computable₂ boundedRun := by
  have he := Nat.Partrec.Code.primrec_evaln.to_comp.comp
    ((Computable.snd.pair (AffineDescription.computable_programCode.comp Computable.fst)).pair
      (AffineDescription.computable_programInput.comp Computable.fst))
  exact Computable.option_map he (AffineDescription.computable_decodeOutput.comp Computable.snd)

theorem boundedRun_sound {p : List Bool} {t : ℕ} {c : AffineCode.Data}
    (h : c ∈ boundedRun p t) : c ∈ AffineDescription.run p := by
  obtain ⟨v, hv, rfl⟩ := Option.mem_map.mp h
  exact Part.mem_map _ (Nat.Partrec.Code.evaln_sound hv)

theorem boundedRun_complete {p : List Bool} {c : AffineCode.Data}
    (h : c ∈ AffineDescription.run p) : ∃ t, c ∈ boundedRun p t := by
  obtain ⟨v, hv, rfl⟩ := (Part.mem_map_iff _).mp h
  obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp hv
  exact ⟨t, Option.mem_map.mpr ⟨v, ht, rfl⟩⟩

/-- Compare the output code and the pool-embedded block at a common finite depth. -/
def eventCheck (d : BlockData) (c : AffineCode.Data) : Bool :=
  StageCodeSearch.check (rank d) (max (bound d) (AffineCode.width c)) (table d) c

theorem computable_eventCheck : Computable₂ eventCheck := by
  have hr : Computable (fun p : BlockData × AffineCode.Data => rank p.1) :=
    primrec_rank.to_comp.comp Computable.fst
  have hn : Computable (fun p : BlockData × AffineCode.Data =>
      max (bound p.1) (AffineCode.width p.2)) :=
    Primrec.nat_max.to_comp.comp (computable_bound.comp Computable.fst)
      (AffineCode.computable_width.comp Computable.snd)
  have hp : Computable₂ (fun p : BlockData × AffineCode.Data => table p.1) :=
    computable_table.comp (Computable.fst.comp Computable.fst) Computable.snd
  exact (StageCodeSearch.computable_check hr hn hp).comp Computable.id Computable.snd

theorem eventCheck_eq_true {d : BlockData} (hd : valid d = true) (c : AffineCode.Data) :
    eventCheck d c = true ↔ AffineCode.valid c = true ∧
      AffineCode.rank c = rank d ∧ AffineCode.event c = (FiniteStageData.block d).event := by
  rw [eventCheck, StageCodeSearch.check_eq_true]
  constructor
  · rintro ⟨hv, hr, hw, ht⟩
    refine ⟨hv, hr, Set.ext fun X => ?_⟩
    rw [← StageFiniteProbability.accepts_code_inputPrefix c _ hw X,
      ht _ (ScanRule.length_inputPrefix X _)]
    exact table_inputPrefix hd _ (Nat.le_max_left _ _) X
  · rintro ⟨hv, hr, he⟩
    refine ⟨hv, hr, Nat.le_max_right _ _, fun v hvlen => ?_⟩
    rw [Bool.eq_iff_iff]
    let X : Cantor := fun k => v.getD k false
    have hprefix : ScanRule.inputPrefix X (max (bound d) (AffineCode.width c)) = v := by
      rw [← hvlen]
      exact StageCodeSearch.inputPrefix_getD v
    have hc := StageFiniteProbability.accepts_code_inputPrefix c
      (max (bound d) (AffineCode.width c)) (Nat.le_max_right _ _) X
    have hd' := table_inputPrefix hd (max (bound d) (AffineCode.width c))
      (Nat.le_max_left _ _) X
    rw [hprefix] at hc hd'
    exact hc.trans (he ▸ hd'.symm)

/-- The total finite checker, including the requested stage and position cutoff. -/
def check (n z : ℕ) (c : Candidate) : Bool :=
  valid (data c) && (above z (data c) && (eventCheck (data c) (output c) &&
    (decide (2 * (program c).length + n + 1 ≤ AffineCode.rank (output c)) &&
      decide (boundedRun (program c) (time c) = some (output c)))))

theorem computable_check : Computable (fun p : (ℕ × ℕ) × Candidate =>
    check p.1.1 p.1.2 p.2) := by
  have hd := primrec_data.to_comp.comp (Computable.snd :
    Computable (fun p : (ℕ × ℕ) × Candidate => p.2))
  have ho := primrec_output.to_comp.comp (Computable.snd :
    Computable (fun p : (ℕ × ℕ) × Candidate => p.2))
  have hp := primrec_program.to_comp.comp (Computable.snd :
    Computable (fun p : (ℕ × ℕ) × Candidate => p.2))
  have ht := primrec_time.to_comp.comp (Computable.snd :
    Computable (fun p : (ℕ × ℕ) × Candidate => p.2))
  have hlen := Computable.list_length.comp hp
  have hbudget := Primrec.nat_le.decide.to_comp.comp
    (Primrec.succ.to_comp.comp (Primrec.nat_add.to_comp.comp
      (Primrec.nat_mul.to_comp.comp (Computable.const 2) hlen)
      (Computable.fst.comp Computable.fst))) (AffineCode.computable_rank.comp ho)
  have heq : Computable₂ (fun x y : Option AffineCode.Data => decide (x = y)) :=
    (Primrec.eq (α := Option AffineCode.Data)).decide.to_comp
  have hrun := heq.comp (computable_boundedRun.comp hp ht)
    (Computable.option_some.comp ho)
  exact Primrec.and.to_comp.comp (computable_valid.comp hd)
    (Primrec.and.to_comp.comp (computable_above.comp (Computable.snd.comp Computable.fst) hd)
      (Primrec.and.to_comp.comp (computable_eventCheck.comp hd ho)
        (Primrec.and.to_comp.comp hbudget hrun)))

/-- The nonprobabilistic obligations certified by a finite candidate. -/
structure Checked (n z : ℕ) (c : Candidate) : Prop where
  valid : FiniteStageData.valid (data c) = true
  above : ∀ p ∈ (block c).support, z ≤ p
  output_valid : AffineCode.valid (output c) = true
  rank : AffineCode.rank (output c) = (block c).rank
  event : AffineCode.event (output c) = (block c).event
  budget : 2 * (program c).length + n + 1 ≤ AffineCode.rank (output c)
  runs : output c ∈ AffineDescription.run (program c)

theorem check_sound {n z : ℕ} {c : Candidate} (h : check n z c = true) : Checked n z c := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hv, ha, he, hb, hr⟩ := h
  obtain ⟨hoc, hrc, hec⟩ := (eventCheck_eq_true hv _).mp he
  exact ⟨hv, support_above ha, hoc, hrc.trans (rank_block hv).symm,
    hec, hb, boundedRun_sound hr⟩

/-- Any mathematically valid finite block and short description pass at some
finite execution bound. This supplies completeness to the stage search. -/
theorem check_complete {n z : ℕ} {d : BlockData} {V : ℕ} {p : List Bool}
    {c : AffineCode.Data} (hd : valid d = true) (ha : ∀ b ∈ pool d, z ≤ b)
    (hc : AffineCode.valid c = true) (hr : AffineCode.rank c = (FiniteStageData.block d).rank)
    (he : AffineCode.event c = (FiniteStageData.block d).event)
    (hb : 2 * p.length + n + 1 ≤ AffineCode.rank c)
    (hp : c ∈ AffineDescription.run p) :
    ∃ t, check n z (d, V, p, c, t) = true := by
  obtain ⟨t, ht⟩ := boundedRun_complete hp
  refine ⟨t, ?_⟩
  have hec := (eventCheck_eq_true hd c).mpr ⟨hc, hr.trans (rank_block hd), he⟩
  have hac := (above_eq_true z d).mpr ha
  have ht' : boundedRun p t = some c := ht
  simp only [check, data, program, output, time, hd, hac, hec, hb, ht',
    decide_true, Bool.and_self]

end Klr.FiniteStageCandidate
