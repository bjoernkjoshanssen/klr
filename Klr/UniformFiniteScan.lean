module

public import Klr.EffectiveEvent
public import Klr.EffectiveQueryCoordinates
public import Klr.StageFiniteScan
public import Klr.StageRankCode
public import Klr.StageChoice

/-!
# Uniform finite computations for indexed scans

All-branch input bounds, finite simulation and pullback of clopen codes are
uniform in an ordinary computable family of fresh scans. Pullback preserves
the fair-coin error of an event name exactly.
-/

@[expose] public section

namespace Klr.UniformFiniteScan

open MeasureTheory RationalPrefixCode
open _root_.Klr.Computability
open scoped symmDiff

local instance : Encodable ℚ := (inferInstance : Primcodable ℚ).toEncodable

variable (π : ℕ → ScanRule)
  (hπ : Computable (fun p : ℕ × List Bool => (π p.1).query p.2))

include hπ

theorem computable_branchBound :
    Computable (fun p : ℕ × ℕ => StageFiniteScan.branchBound (π p.1) p.2) := by
  have hq : Computable (fun p : (ℕ × ℕ) × List Bool => (π p.1.1).query p.2 + 1) :=
    Computable.succ.comp
      (hπ.comp ((Computable.fst.comp Computable.fst).pair Computable.snd))
  have hi : Computable (fun p : ℕ × ℕ =>
      ((SparseSearch.words p.2).map (fun v => (π p.1).query v + 1)).sum) :=
    StageFiniteScan.computable_list_sum
      (l := fun p : ℕ × ℕ => SparseSearch.words p.2)
      (f := fun p v => (π p.1).query v + 1)
      (SparseSearch.computable_words.comp Computable.snd) hq
  have hf : Computable (fun p : (ℕ × ℕ) × ℕ =>
      ((SparseSearch.words p.2).map (fun v => (π p.1.1).query v + 1)).sum) :=
    Computable.comp (f := fun p : ℕ × ℕ =>
      ((SparseSearch.words p.2).map (fun v => (π p.1).query v + 1)).sum)
      (g := fun p : (ℕ × ℕ) × ℕ => (p.1.1, p.2)) hi
      ((Computable.fst.comp Computable.fst).pair Computable.snd)
  exact StageFiniteScan.computable_list_sum
    (l := fun p : ℕ × ℕ => List.range p.2)
    (f := fun p t => ((SparseSearch.words t).map (fun v => (π p.1).query v + 1)).sum)
    (Primrec.list_range.to_comp.comp Computable.snd) hf

theorem computable_run :
    Computable (fun p : (ℕ × List Bool) × ℕ => StageFiniteScan.run (π p.1.1) p.1.2 p.2) := by
  have hp : Computable (fun p : ((ℕ × List Bool) × ℕ) × (ℕ × List Bool) => p.2.2) :=
    Computable.snd.comp Computable.snd
  have hi : Computable (fun p : ((ℕ × List Bool) × ℕ) × (ℕ × List Bool) => p.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hs : Computable (fun p : ((ℕ × List Bool) × ℕ) × (ℕ × List Bool) => p.1.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  have hb := (Primrec.list_getD false).to_comp.comp hs (hπ.comp (hi.pair hp))
  have hstep := Computable.list_append.comp hp
    (Primrec.list_cons.to_comp.comp hb (Computable.const []))
  apply (Computable.nat_rec Computable.snd (Computable.const []) hstep.to₂).of_eq
  intro p
  induction p.2 with
  | zero => rfl
  | succ t ih =>
    simpa only [StageFiniteScan.run, ScanRule.transcript_succ, Nat.rec_add_one] using
      congrArg (fun v => v ++ [p.1.2.getD ((π p.1.1).query v) false]) ih

omit hπ in
/-- Pull a finite answer-space table back to actual inputs. -/
def pullback (i : ℕ) (c : Code) : Code :=
  ofTable (StageFiniteScan.branchBound (π i) c.1)
    (fun s => value c (StageFiniteScan.run (π i) s c.1))

theorem computable_pullback : Computable₂ (pullback π) := by
  apply computable_ofTable
    ((computable_branchBound π hπ).comp
      (Computable.fst.pair (Computable.fst.comp Computable.snd)))
  have hr : Computable (fun p : (ℕ × Code) × List Bool =>
      StageFiniteScan.run (π p.1.1) p.2 p.1.2.1) :=
    Computable.comp (f := fun p : (ℕ × List Bool) × ℕ =>
      StageFiniteScan.run (π p.1.1) p.1.2 p.2)
      (g := fun p : (ℕ × Code) × List Bool => ((p.1.1, p.2), p.1.2.1))
      (computable_run π hπ)
      (((Computable.fst.comp Computable.fst).pair Computable.snd).pair
        (Computable.fst.comp (Computable.snd.comp Computable.fst)))
  exact primrec_value.to_comp.comp (Computable.snd.comp Computable.fst) hr

omit hπ in
@[simp] theorem eval_pullback (i : ℕ) (c : Code) (X : Cantor) :
    eval (pullback π i c) X = eval c ((π i).observationMap X) := by
  rw [pullback, eval_ofTable, StageFiniteScan.run_inputPrefix_of_bound (π i) c.1
    _ (StageFiniteScan.query_lt_branchBound (π i) c.1) X le_rfl]
  rw [eval, (π i).inputPrefix_observationMap]

omit hπ in
@[simp] theorem event_pullback (i : ℕ) (c : Code) :
    event (pullback π i c) = (π i).observationMap ⁻¹' event c := by
  ext X
  simp [event]

omit hπ in
theorem measureReal_preimage (i : ℕ) {S : Set Cantor} (hS : MeasurableSet S) :
    fairCoin.real ((π i).observationMap ⁻¹' S) = fairCoin.real S := by
  rw [← map_measureReal_apply (π i).measurable_observationMap hS,
    StageChoice.fairCoin_map_observationMap]

/-- Observation pullback preserves the same oracle and the same accuracy. -/
def pullbackName {A : Oracle} {α : Type*} [Primcodable α]
    {S : α → Set Cantor} (N : EffectiveEvent.Name A S)
    {i : α → ℕ} (hi : ComputableIn {oracleFunction A} i) :
    EffectiveEvent.Name A (fun a => (π (i a)).observationMap ⁻¹' S a) where
  code a k := pullback π (i a) (N.code a k)
  computable := RelativeComputable.comp₂ (computable_pullback π hπ).computableIn
    (RelativeComputable.comp hi ComputableIn.fst) N.computable
  measurable a := (π (i a)).measurable_observationMap (N.measurable a)
  error a k := by
    rw [event_pullback, ← Set.preimage_symmDiff,
      measureReal_preimage π (i a) ((measurableSet_event _).symmDiff (N.measurable a))]
    exact N.error a k

/-- The finite unread mask is uniform in the family index. -/
theorem computable_unreadMask :
    Computable (fun p : (ℕ × List ℕ) × List Bool =>
      StageRankCode.unreadMask (π p.1.1) p.1.2 p.2) := by
  have hi : Computable (fun p : ((ℕ × List ℕ) × List Bool) × ℕ => p.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hG : Computable (fun p : ((ℕ × List ℕ) × List Bool) × ℕ => p.1.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  have hv : Computable (fun p : ((ℕ × List ℕ) × List Bool) × ℕ => p.1.2) :=
    Computable.snd.comp Computable.fst
  have ha := (Primrec.list_getD 0).to_comp.comp hG Computable.snd
  have hr := EffectiveQueryCoordinates.computable_reads π hπ hi ha
    (Computable.list_length.comp hv) hv
  have ht := (SparseSearch.computable_tabulate
    (f := fun p : (ℕ × List ℕ) × List Bool => fun j =>
      !EffectiveQueryCoordinates.reads π p.1.1 (p.1.2.getD j 0) p.2.length p.2)
    (Primrec.not.to_comp.comp hr).to₂).comp
      (Computable.id.pair (Computable.list_length.comp (Computable.snd.comp Computable.fst)))
  apply ht.of_eq
  intro p
  rfl

theorem computable_dropTest :
    Computable (fun p : ((ℕ × List ℕ) × AffineCode.Data) × List Bool =>
      StageRankCode.dropTest (π p.1.1.1) p.1.1.2 p.1.2 p.2) := by
  have hm : Computable (fun p : ((ℕ × List ℕ) × AffineCode.Data) × List Bool =>
      StageRankCode.unreadMask (π p.1.1.1) p.1.1.2 p.2) :=
    Computable.comp (f := fun p : (ℕ × List ℕ) × List Bool =>
      StageRankCode.unreadMask (π p.1.1) p.1.2 p.2)
      (g := fun p : ((ℕ × List ℕ) × AffineCode.Data) × List Bool => (p.1.1, p.2))
      (computable_unreadMask π hπ)
      ((Computable.fst.comp Computable.fst).pair Computable.snd)
  exact Primrec.not.to_comp.comp
    (SparseSearch.computable_maskedFullRank.comp
      (Computable.snd.comp Computable.fst) hm)

theorem computable_partialTest :
    Computable (fun p : ((ℕ × List ℕ) × AffineCode.Data) × List Bool =>
      StageRankCode.partialTest (π p.1.1.1) p.1.1.2 p.1.2 p.2) := by
  have hm : Computable (fun p : ((ℕ × List ℕ) × AffineCode.Data) × List Bool =>
      StageRankCode.unreadMask (π p.1.1.1) p.1.1.2 p.2) :=
    Computable.comp (f := fun p : (ℕ × List ℕ) × List Bool =>
      StageRankCode.unreadMask (π p.1.1) p.1.2 p.2)
      (g := fun p : ((ℕ × List ℕ) × AffineCode.Data) × List Bool => (p.1.1, p.2))
      (computable_unreadMask π hπ)
      ((Computable.fst.comp Computable.fst).pair Computable.snd)
  have hz : Computable (fun p : ((ℕ × List ℕ) × AffineCode.Data) × List Bool =>
      StageRankCode.zeroRankTest (π p.1.1.1) p.1.1.2 p.1.2 p.2) :=
    StageRankCode.computable_zeroMatrix.comp
    (SparseSearch.computable_maskCode.comp (Computable.snd.comp Computable.fst) hm)
  exact Primrec.and.to_comp.comp (Primrec.not.to_comp.comp hz)
    (computable_dropTest π hπ)

end Klr.UniformFiniteScan
