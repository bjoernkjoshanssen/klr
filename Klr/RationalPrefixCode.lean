module

public import Klr.PoolAdviceComputable
public import Klr.PoolAdviceMeasure
public import Klr.PoolAdviceTables
public import Klr.HighSetApproximation
public import Klr.Computability.RelativeComputable
public import Mathlib.MeasureTheory.Function.L1Space.AEEqFun

/-!
# Effective finite rational prefix tables

A code is an ordinary pair consisting of a depth and a finite rational list.
Its entries use the existing encoding of finite Boolean words. Full tables
can be tabulated effectively, and their exact L1 distances are rational
finite averages. Thresholding such a table gives an actual clopen set.
-/

@[expose] public section

namespace Klr.RationalPrefixCode

open MeasureTheory SparseSearch RationalComputability Filter
open scoped Topology symmDiff

local instance : Encodable ℚ := (inferInstance : Primcodable ℚ).toEncodable

/-- The first component is the input depth, the second the rational lookup table. -/
abbrev Code := ℕ × List ℚ

/-- Evaluate a coded table on a finite word, ignoring later bits. -/
def value (c : Code) (s : List Bool) : ℚ :=
  c.2.getD (Encodable.encode (s.take c.1)) 0

/-- Evaluate a coded table on a Cantor-space point. -/
def eval (c : Code) (X : Cantor) : ℚ := value c (ScanRule.inputPrefix X c.1)

theorem primrec_value : Primrec₂ value := by
  exact (Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.fst)
    (Primrec.encode.comp (Primrec.list_take.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd))

@[simp] theorem value_inputPrefix (c : Code) (X : Cantor) {d : ℕ} (hd : c.1 ≤ d) :
    value c (ScanRule.inputPrefix X d) = eval c X := by
  simp only [value, eval, PoolAdvice.inputPrefix_take X hd,
    PoolAdvice.inputPrefix_take X (le_refl c.1)]

/-- The equivalent finite-type table, convenient for analytic APIs. -/
def table (c : Code) (u : Fin c.1 → Bool) : ℚ := value c (List.ofFn u)

@[simp] theorem eval_table (c : Code) (X : Cantor) :
    PoolApproximation.eval (table c) X = eval c X := by
  simp [PoolApproximation.eval, table, eval, PoolAdvice.inputPrefix_eq_ofFn]

theorem measurable_eval (c : Code) : Measurable (fun X => (eval c X : ℝ)) := by
  convert PoolApproximation.measurable_eval (fun u => (table c u : ℝ)) using 1
  funext X
  exact congrArg Rat.cast (eval_table c X).symm

theorem integrable_eval (c : Code) : Integrable (fun X => (eval c X : ℝ)) fairCoin :=
  PoolAdvice.integrable_prefixFunction c.1 (fun s => (value c s : ℝ))

/-- A computable bound on every word code at the given depth. -/
def wordBound (d : ℕ) : ℕ := ((words d).map Encodable.encode).sum + 1

theorem computable_wordBound : Computable wordBound := by
  have hm : Primrec (fun l : List (List Bool) => l.map Encodable.encode) :=
    Primrec.list_map Primrec.id (Primrec.encode.comp Primrec.snd).to₂
  exact Computable.succ.comp ((Primrec.list_sum Primrec.id).to_comp.comp
    (hm.to_comp.comp computable_words))

theorem encode_lt_wordBound {d : ℕ} {s : List Bool} (hs : s.length = d) :
    Encodable.encode s < wordBound d := by
  apply Nat.lt_succ_of_le
  apply List.le_sum_of_mem
  exact List.mem_map.mpr ⟨s, (mem_words_iff d s).mpr hs, rfl⟩

/-- Total word decoding is harmless away from the actual table indices. -/
def word (n : ℕ) : List Bool := (Encodable.decode n).getD []

theorem primrec_word : Primrec word :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

@[simp] theorem word_encode (s : List Bool) : word (Encodable.encode s) = s := by
  simp [word]

/-- Build a complete table from its depth and values on finite words. -/
def ofTable (d : ℕ) (q : List Bool → ℚ) : Code :=
  (d, (List.range (wordBound d)).map (fun n => q (word n)))

@[simp] theorem value_ofTable {d : ℕ} (q : List Bool → ℚ) {s : List Bool}
    (hs : s.length = d) : value (ofTable d q) s = q s := by
  have hb := encode_lt_wordBound hs
  simp only [value, ofTable, List.take_of_length_le hs.le,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, hb,
    Option.map_some, Option.getD_some, word_encode]

@[simp] theorem eval_ofTable (d : ℕ) (q : List Bool → ℚ) (X : Cantor) :
    eval (ofTable d q) X = q (ScanRule.inputPrefix X d) :=
  value_ofTable q (ScanRule.length_inputPrefix X d)

/-- Uniform oracle computation of a finite table does not cost another jump. -/
theorem computableIn_ofTable {α : Type*} [Primcodable α] [Inhabited α]
    {O : Set (ℕ →. ℕ)} {d : α → ℕ} {q : α → List Bool → ℚ}
    (hd : ComputableIn O d) (hq : ComputableIn₂ O q) :
    ComputableIn O (fun a => ofTable (d a) (q a)) := by
  have hv : ComputableIn₂ O (fun a n => q a (word n)) :=
    Computability.RelativeComputable.comp₂ hq ComputableIn.fst
      (Computability.RelativeComputable.comp primrec_word.computableIn ComputableIn.snd)
  have ht := Computability.RelativeComputable.comp
    (Computability.RelativeComputable.tabulate hv)
    (Computability.RelativeComputable.pair ComputableIn.id
      (Computability.RelativeComputable.comp computable_wordBound.computableIn hd))
  exact Computability.RelativeComputable.pair hd ht

theorem computable_ofTable {α : Type*} [Primcodable α] [Inhabited α]
    {d : α → ℕ} {q : α → List Bool → ℚ}
    (hd : Computable d) (hq : Computable₂ q) :
    Computable (fun a => ofTable (d a) (q a)) :=
  recursiveIn_empty_iff.mp (computableIn_ofTable hd.computableIn hq.computableIn)

/-- The exact rational L1 distance between two prefix tables. -/
def distance (c e : Code) : ℚ :=
  PoolAdvice.average (max c.1 e.1) (fun s => |value c s - value e s|)

theorem computable_distance : Computable₂ distance := by
  apply PoolAdvice.computable_average
    (Primrec.nat_max.to_comp.comp (Computable.fst.comp Computable.fst)
      (Computable.fst.comp Computable.snd))
  exact PoolAdvice.computable_rat_abs.comp
    (primrec_rat_sub.to_comp.comp
      (primrec_value.to_comp.comp (Computable.fst.comp Computable.fst) Computable.snd)
      (primrec_value.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd))

theorem distance_eq_integral (c e : Code) :
    (distance c e : ℝ) = ∫ X, ‖(eval c X : ℝ) - (eval e X : ℝ)‖ ∂fairCoin := by
  rw [distance, PoolAdvice.average_eq_integral]
  congr 1
  funext X
  rw [value_inputPrefix c X (Nat.le_max_left _ _),
    value_inputPrefix e X (Nat.le_max_right _ _)]
  simp

noncomputable section

/-- The actual L1 function represented by a finite rational code. -/
def toL1 (c : Code) : Lp ℝ 1 fairCoin := (integrable_eval c).toL1 (fun X => (eval c X : ℝ))

theorem dist_toL1_eq_integral {f g : Cantor → ℝ}
    (hf : Integrable f fairCoin) (hg : Integrable g fairCoin) :
    dist (hf.toL1 f) (hg.toL1 g) = ∫ X, ‖f X - g X‖ ∂fairCoin := by
  rw [dist_eq_norm, ← Integrable.toL1_sub, Integrable.norm_toL1_eq_lintegral_eNorm]
  simpa only [Pi.sub_apply] using
    (integral_norm_eq_lintegral_eNorm (hf.sub hg).aestronglyMeasurable).symm

theorem dist_toL1 (c e : Code) : dist (toL1 c) (toL1 e) = (distance c e : ℝ) := by
  rw [toL1, toL1, dist_toL1_eq_integral, distance_eq_integral]

theorem tendsto_toL1 {c : ℕ → Code} {g : Cantor → ℝ} (hg : Integrable g fairCoin)
    (h : Tendsto (fun n => ∫ X, ‖(eval (c n) X : ℝ) - g X‖ ∂fairCoin) atTop (𝓝 0)) :
    Tendsto (fun n => toL1 (c n)) atTop (𝓝 (hg.toL1 g)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  simpa only [toL1, dist_toL1_eq_integral] using h

end

/-- The clopen set obtained by thresholding a rational table at one half. -/
def event (c : Code) : Set Cantor := {X | (1 / 2 : ℚ) < eval c X}

theorem event_eq_table (c : Code) :
    event c = PoolApproximation.event (HighSetApproximation.threshold (table c)) := by
  ext X
  simp [event, PoolApproximation.event, HighSetApproximation.threshold,
    ← eval_table c X, PoolApproximation.eval]

theorem measurableSet_event (c : Code) : MeasurableSet (event c) := by
  rw [event_eq_table]
  exact PoolApproximation.measurableSet_event _

theorem isClopen_event (c : Code) : IsClopen (event c) := by
  let f : (Fin c.1 → Bool) → Bool := HighSetApproximation.threshold (table c)
  have hb : Continuous (PoolApproximation.bits c.1) :=
    continuous_pi (fun i => continuous_apply i.val)
  have hf : Continuous f := continuous_of_discreteTopology
  rw [event_eq_table]
  exact (isClopen_discrete {true}).preimage (hf.comp hb)

theorem event_eq_iUnion (c : Code) :
    event c = ⋃ s ∈ (words c.1).toFinset,
      if (1 / 2 : ℚ) < value c s then cylinder s else ∅ := by
  ext X
  simp only [Set.mem_iUnion, List.mem_toFinset, mem_words_iff]
  constructor
  · intro h
    change (1 / 2 : ℚ) < value c (ScanRule.inputPrefix X c.1) at h
    refine ⟨ScanRule.inputPrefix X c.1, ScanRule.length_inputPrefix X c.1, ?_⟩
    simpa only [h, ite_true] using ScanRule.mem_cylinder_inputPrefix X c.1
  · rintro ⟨s, hs, hmem⟩
    have hp : (1 / 2 : ℚ) < value c s ∧ X ∈ cylinder s := by
      split_ifs at hmem with h
      · exact ⟨h, hmem⟩
      · exact False.elim hmem
    obtain ⟨h, hX⟩ := hp
    rwa [← (PoolAdvice.inputPrefix_eq_iff_mem_cylinder X c.1 s hs).mpr hX] at h

theorem measureReal_symmDiff_event_le (c : Code) {H : Set Cantor}
    (hH : MeasurableSet H) :
    fairCoin.real (event c ∆ H) ≤
      2 * ∫ X, ‖(eval c X : ℝ) - H.indicator (fun _ => (1 : ℝ)) X‖ ∂fairCoin := by
  simpa only [← event_eq_table, eval_table] using
    HighSetApproximation.measureReal_symmDiff_threshold_le hH (table c)

/-- Applying a computable rational function to a table preserves its depth. -/
def map (f : ℚ → ℚ) (c : Code) : Code :=
  ofTable c.1 (fun s => f (value c s))

theorem computable_map {f : ℚ → ℚ} (hf : Computable f) : Computable (map f) :=
  computable_ofTable Computable.fst (hf.comp primrec_value.to_comp)

@[simp] theorem eval_map (f : ℚ → ℚ) (c : Code) (X : Cantor) :
    eval (map f c) X = f (eval c X) := by simp [map]

/-- Combine two tables at their common prefix depth. -/
def zip (f : ℚ → ℚ → ℚ) (c e : Code) : Code :=
  ofTable (max c.1 e.1) (fun s => f (value c s) (value e s))

theorem computable_zip {f : ℚ → ℚ → ℚ} (hf : Computable₂ f) : Computable₂ (zip f) := by
  apply computable_ofTable
    (Primrec.nat_max.to_comp.comp (Computable.fst.comp Computable.fst)
      (Computable.fst.comp Computable.snd))
  exact hf.comp
    (primrec_value.to_comp.comp (Computable.fst.comp Computable.fst) Computable.snd)
    (primrec_value.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd)

@[simp] theorem eval_zip (f : ℚ → ℚ → ℚ) (c e : Code) (X : Cantor) :
    eval (zip f c e) X = f (eval c X) (eval e X) := by
  simp only [zip, eval_ofTable, value_inputPrefix c X (Nat.le_max_left _ _),
    value_inputPrefix e X (Nat.le_max_right _ _)]

/-- Rational ramps are exact finite-table operations, including at slope zero. -/
def ramp (m : ℕ) (c : Code) : Code :=
  map (fun q => max 0 (1 - (m : ℚ) * (1 - q))) c

theorem computable_ramp : Computable₂ ramp := by
  apply computable_ofTable (Computable.fst.comp Computable.snd)
  have hv : Computable (fun p : (ℕ × Code) × List Bool => value p.1.2 p.2) :=
    primrec_value.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd
  exact primrec_rat_max.to_comp.comp (Computable.const 0)
    (primrec_rat_sub.to_comp.comp (Computable.const 1)
      (primrec_rat_mul.to_comp.comp
        (primrec_rat_natCast.to_comp.comp (Computable.fst.comp Computable.fst))
        (primrec_rat_sub.to_comp.comp (Computable.const 1) hv)))

@[simp] theorem cast_eval_ramp (m : ℕ) (c : Code) (X : Cantor) :
    (eval (ramp m c) X : ℝ) = HighSetApproximation.ramp m (eval c X : ℝ) := by
  simp [ramp, HighSetApproximation.ramp]

/-- A zero-one table for the complement of the coded event. -/
def compl (c : Code) : Code := map (fun q => if (1 / 2 : ℚ) < q then 0 else 1) c

theorem computable_compl : Computable compl := by
  apply computable_map
  exact (Primrec.ite (primrec_rat_le.comp Primrec.id (Primrec.const (1 / 2)))
    (Primrec.const (1 : ℚ)) (Primrec.const 0)).to_comp.of_eq fun q => by
      split_ifs <;> simp_all; linarith

@[simp] theorem event_compl (c : Code) : event (compl c) = (event c)ᶜ := by
  ext X
  simp only [event, compl, eval_map, Set.mem_ofPred_eq, Set.mem_compl_iff]
  split_ifs <;> norm_num <;> linarith

/-- A zero-one table for the intersection of two coded events. -/
def inter (c e : Code) : Code :=
  zip (fun q r => if (1 / 2 : ℚ) < q ∧ (1 / 2 : ℚ) < r then 1 else 0) c e

theorem computable_inter : Computable₂ inter := by
  apply computable_zip
  have hq : PrimrecPred (fun p : ℚ × ℚ => ¬p.1 ≤ 1 / 2) :=
    (primrec_rat_le.comp Primrec.fst (Primrec.const (1 / 2))).not
  have hr : PrimrecPred (fun p : ℚ × ℚ => ¬p.2 ≤ 1 / 2) :=
    (primrec_rat_le.comp Primrec.snd (Primrec.const (1 / 2))).not
  exact (Primrec.ite (hq.and hr) (Primrec.const (1 : ℚ)) (Primrec.const 0)).to_comp.of_eq
    fun p => by simp

@[simp] theorem event_inter (c e : Code) : event (inter c e) = event c ∩ event e := by
  ext X
  simp only [event, inter, eval_zip, Set.mem_ofPred_eq, Set.mem_inter_iff]
  split_ifs <;> norm_num at * <;> tauto

end Klr.RationalPrefixCode
