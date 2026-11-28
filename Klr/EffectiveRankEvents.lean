module

public import Klr.UniformFiniteScan
public import Klr.FiniteStageData
public import Klr.StageRankLimit

/-!
# Uniform effective names for rank events

Loss of full unread rank by a finite horizon is an actual computable clopen
event. Its increasing union, the event of any rank drop, therefore has a
uniform first-jump name in measure. Complements and finite-horizon subtraction
give the no-drop and first-drop-tail events without another jump.
-/

@[expose] public section

namespace Klr.EffectiveRankEvents

open MeasureTheory RationalPrefixCode FiniteStageData
open _root_.Klr.Computability

local instance : Encodable ℚ := (inferInstance : Primcodable ℚ).toEncodable

abbrev Input := ℕ × BlockData

variable (π : ℕ → ScanRule)

/-- Invalid finite block data use the empty-block convention. -/
def test (p : Input) (v : List Bool) : Bool :=
  valid p.2 && StageRankCode.dropTest (π p.1) (pool p.2) (entry p.2).2 v

theorem test_eq_true (p : Input) (v : List Bool) :
    test π p v = true ↔ (block p.2).remainingRank (π p.1) v < (block p.2).rank := by
  by_cases h : valid p.2 = true
  · rw [test, h, Bool.true_and, block_of_valid p.2 h]
    exact StageRankCode.dropTest_eq_true (π p.1) (pool p.2)
      ((valid_eq_true p.2).mp h).1 (entry p.2) ((valid_eq_true p.2).mp h).2
      (SparseSearch.wordVector (rank p.2) (syndrome p.2)) v
  · have hf : valid p.2 = false := Bool.eq_false_iff.mpr h
    simp [test, hf, block, StageRecursion.emptyBlock]

variable (hπ : Computable (fun p : ℕ × List Bool => (π p.1).query p.2))

include hπ in
theorem computable_test : Computable₂ (test π) := by
  have harg : Primrec (fun p : Input × List Bool =>
      (((p.1.1, pool p.1.2), (entry p.1.2).2), p.2)) :=
    (((Primrec.fst.comp Primrec.fst).pair
      (primrec_pool.comp (Primrec.snd.comp Primrec.fst))).pair
        (Primrec.snd.comp (primrec_entry.comp (Primrec.snd.comp Primrec.fst)))).pair
          Primrec.snd
  have hr : Computable (fun p : Input × List Bool =>
      StageRankCode.dropTest (π p.1.1) (pool p.1.2) (entry p.1.2).2 p.2) :=
    Computable.comp (f := fun p : ((ℕ × List ℕ) × AffineCode.Data) × List Bool =>
      StageRankCode.dropTest (π p.1.1.1) p.1.1.2 p.1.2 p.2)
      (g := fun p : Input × List Bool =>
        (((p.1.1, pool p.1.2), (entry p.1.2).2), p.2))
      (UniformFiniteScan.computable_dropTest π hπ) harg.to_comp
  have hv : Computable (fun p : Input × List Bool => valid p.1.2) :=
    Computable.comp (f := valid) (g := fun p : Input × List Bool => p.1.2)
      computable_valid (Computable.snd.comp Computable.fst)
  exact Primrec.and.to_comp.comp hv hr

def answerCode (p : Input) (V : ℕ) : Code :=
  ofTable V (fun v => if test π p v then 1 else 0)

include hπ in
theorem computable_answerCode : Computable₂ (answerCode π) := by
  have ht : Computable (fun p : (Input × ℕ) × List Bool => test π p.1.1 p.2) :=
    Computable₂.comp (f := test π) (computable_test π hπ)
      (Computable.fst.comp Computable.fst) Computable.snd
  apply computable_ofTable (d := fun p : Input × ℕ => p.2)
    (q := fun p v => if test π p.1 v then 1 else 0) Computable.snd
  exact (Computable.cond ht (Computable.const (1 : ℚ)) (Computable.const 0)).of_eq
    fun _ => by simp only [Bool.cond_eq_ite]

/-- The finite drop event is encoded on input bits, not just prescribed answers. -/
def droppedCode (p : Input) (V : ℕ) : Code :=
  UniformFiniteScan.pullback π p.1 (answerCode π p V)

include hπ in
theorem computable_droppedCode : Computable₂ (droppedCode π) :=
  Computable₂.comp (f := UniformFiniteScan.pullback π)
    (UniformFiniteScan.computable_pullback π hπ)
    (Computable.fst.comp Computable.fst) (computable_answerCode π hπ)

@[simp] theorem event_droppedCode (p : Input) (V : ℕ) :
    event (droppedCode π p V) = StageRankLimit.droppedBy (block p.2) (π p.1) V := by
  ext X
  simp only [event, droppedCode, UniformFiniteScan.eval_pullback, answerCode,
    eval_ofTable, (π p.1).inputPrefix_observationMap, Set.mem_ofPred_eq,
    StageRankLimit.mem_droppedBy_iff]
  have ht := test_eq_true π p ((π p.1).transcript X V)
  split_ifs with h
  · simpa only [ht.mp h, iff_true] using (by norm_num : (1 / 2 : ℚ) < 1)
  · simpa only [mt ht.mpr h, iff_false] using (by norm_num : ¬(1 / 2 : ℚ) < 0)

noncomputable section

include hπ in
/-- Any rank drop has a uniform first-jump clopen approximation in measure. -/
def dropName : EffectiveEvent.Name (OracleJump.zeroJump 1)
    (fun p : Input => LateDropBound.hasDrop (block p.2) (π p.1)) := by
  let N := Classical.choice (EffectiveEvent.exists_name_iUnion (A := OracleJump.zeroJump 0)
    (computable_droppedCode π hπ).computableIn (fun p => by
      simpa only [event_droppedCode] using StageRankLimit.droppedBy_mono (block p.2) (π p.1)))
  simpa only [event_droppedCode, StageRankLimit.iUnion_droppedBy,
    ← OracleJump.zeroJump_succ 0] using N

include hπ in
def noDropName : EffectiveEvent.Name (OracleJump.zeroJump 1)
    (fun p : Input => NoDrop.noDropEvent (block p.2) (π p.1)) := by
  simpa only [LateDropBound.hasDrop, compl_compl] using (dropName π hπ).compl

include hπ in
def tailName : EffectiveEvent.Name (OracleJump.zeroJump 1)
    (fun p : Input × ℕ => StoppingTranscript.rankDropTailEvent (block p.1.2) (π p.1.1) p.2) := by
  let N := (dropName π hπ).reindex (f := fun p : Input × ℕ => p.1) ComputableIn.fst
  let M := EffectiveEvent.ofClopen (A := OracleJump.zeroJump 1)
    (computable_droppedCode π hπ).computableIn
  have he (p : Input × ℕ) :
      LateDropBound.hasDrop (block p.1.2) (π p.1.1) ∩
        (event (droppedCode π p.1 p.2))ᶜ =
        StoppingTranscript.rankDropTailEvent (block p.1.2) (π p.1.1) p.2 := by
    rw [event_droppedCode, StageRankLimit.rankDropTailEvent_eq_sdiff]
    rfl
  exact (show (fun p : Input × ℕ =>
    LateDropBound.hasDrop (block p.1.2) (π p.1.1) ∩
      (event (droppedCode π p.1 p.2))ᶜ) = _ from funext he) ▸ (N.inter M.compl)

end

end Klr.EffectiveRankEvents
