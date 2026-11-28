module

public import Klr.EffectiveEvent
public import Klr.EffectiveBlockProduct

/-!
# Effective probabilities under finite affine conditions

A finite affine header is itself an exact clopen code. Intersecting its event
with an event name and dividing by the exact rational header mass computes
the desired conditional probability, in the same oracle. The explicit error
is the original dyadic error divided by that mass. This includes null headers,
where both the conditional law and the rational quotients are zero.
-/

@[expose] public section

namespace Klr.EffectiveConditionalEvent

open MeasureTheory ProbabilityTheory RationalPrefixCode
open _root_.Klr.Computability
open scoped Topology symmDiff

local instance : Encodable ℚ := (inferInstance : Primcodable ℚ).toEncodable

def depth (cs : List AffineCode.Data) : ℕ := (cs.map AffineCode.width).sum

theorem computable_depth : Computable depth := by
  have hw : Primrec AffineCode.width := Primrec.fst.comp Primrec.fst
  exact (Primrec.list_sum (Primrec.list_map Primrec.id (hw.comp Primrec.snd).to₂)).to_comp

theorem width_le_depth (cs : List AffineCode.Data) (c : AffineCode.Data) (hc : c ∈ cs) :
    AffineCode.width c ≤ depth cs :=
  List.le_sum_of_mem (List.mem_map.mpr ⟨c, hc, rfl⟩)

/-- One actual finite code for the conjunction of all affine equations. -/
def conditionCode (cs : List AffineCode.Data) : Code :=
  ofTable (depth cs) (fun s => if StageFiniteProbability.accepts cs s then 1 else 0)

theorem computable_conditionCode : Computable conditionCode := by
  apply computable_ofTable computable_depth
  exact (Computable.cond StageFiniteProbability.computable_accepts
    (Computable.const (1 : ℚ)) (Computable.const 0)).of_eq fun _ => by
      simp only [Bool.cond_eq_ite]

@[simp] theorem event_conditionCode (cs : List AffineCode.Data) :
    event (conditionCode cs) = StageFiniteProbability.event cs := by
  ext X
  simp only [event, conditionCode, eval_ofTable, Set.mem_ofPred_eq]
  have ha := StageFiniteProbability.accepts_inputPrefix cs (depth cs)
    (width_le_depth cs) X
  split_ifs with h
  · simpa only [ha.mp h, iff_true] using (by norm_num : (1 / 2 : ℚ) < 1)
  · simpa only [mt ha.mpr h, iff_false] using (by norm_num : ¬(1 / 2 : ℚ) < 0)

/-- The exact rational mass of the finite conditioning event. -/
def denominator (cs : List AffineCode.Data) : ℚ :=
  EffectiveEvent.probability (conditionCode cs)

theorem computable_denominator : Computable denominator :=
  EffectiveEvent.computable_probability.comp computable_conditionCode

theorem denominator_eq (cs : List AffineCode.Data) :
    (denominator cs : ℝ) = fairCoin.real (StageFiniteProbability.event cs) := by
  rw [denominator, EffectiveEvent.probability_eq_measureReal, event_conditionCode]

theorem denominator_nonneg (cs : List AffineCode.Data) : 0 ≤ denominator cs := by
  apply (Rat.cast_nonneg (K := ℝ)).mp
  rw [denominator_eq]
  exact measureReal_nonneg

/-- Exact probability of a coded clopen event under the finite conditional law. -/
def probability (cs : List AffineCode.Data) (c : Code) : ℚ :=
  EffectiveEvent.probability (RationalPrefixCode.inter (conditionCode cs) c) / denominator cs

theorem computable_probability : Computable₂ probability := by
  have hn : Computable (fun p : List AffineCode.Data × Code =>
      EffectiveEvent.probability (RationalPrefixCode.inter (conditionCode p.1) p.2)) :=
    EffectiveEvent.computable_probability.comp
      (computable_inter.comp (computable_conditionCode.comp Computable.fst) Computable.snd)
  exact RationalComputability.primrec_rat_div.to_comp.comp hn
    (computable_denominator.comp Computable.fst)

theorem real_law (cs : List AffineCode.Data) (S : Set Cantor) :
    (StageFiniteProbability.law cs).real S =
      fairCoin.real (StageFiniteProbability.event cs ∩ S) / (denominator cs : ℝ) := by
  rw [StageFiniteProbability.law, measureReal_def,
    cond_apply (StageFiniteProbability.measurableSet_event cs), ENNReal.toReal_mul,
    ENNReal.toReal_inv, denominator_eq, div_eq_mul_inv, mul_comm]
  rfl

theorem probability_eq (cs : List AffineCode.Data) (c : Code) :
    (probability cs c : ℝ) = (StageFiniteProbability.law cs).real (event c) := by
  rw [probability, Rat.cast_div, EffectiveEvent.probability_eq_measureReal,
    event_inter, event_conditionCode, real_law]

namespace Name

variable {α : Type*} [Primcodable α] {A : Oracle} {S : α → Set Cantor}

def approximation (N : EffectiveEvent.Name A S) (cs : α → List AffineCode.Data)
    (a : α) (k : ℕ) : ℚ := probability (cs a) (N.code a k)

def error (cs : α → List AffineCode.Data) (a : α) (k : ℕ) : ℚ :=
  CauchyModulus.dyadic k / denominator (cs a)

theorem approximation_computable (N : EffectiveEvent.Name A S)
    {cs : α → List AffineCode.Data} (hcs : ComputableIn {oracleFunction A} cs) :
    ComputableIn₂ {oracleFunction A} (approximation N cs) := by
  exact RelativeComputable.comp₂ (f := probability)
    (g := fun p : α × ℕ => cs p.1) (h := fun p : α × ℕ => N.code p.1 p.2)
    computable_probability.computableIn
    (RelativeComputable.comp (f := cs) hcs ComputableIn.fst) N.computable

theorem error_computable {cs : α → List AffineCode.Data}
    (hcs : ComputableIn {oracleFunction A} cs) :
    ComputableIn₂ {oracleFunction A} (error cs) := by
  have hd : ComputableIn {oracleFunction A} (fun p : α × ℕ => denominator (cs p.1)) :=
    RelativeComputable.comp (f := denominator) computable_denominator.computableIn
      (RelativeComputable.comp (f := cs) hcs ComputableIn.fst)
  exact RelativeComputable.comp₂ (f := fun q r : ℚ => q / r)
    (g := fun p : α × ℕ => CauchyModulus.dyadic p.2)
    (h := fun p : α × ℕ => denominator (cs p.1))
    RationalComputability.primrec_rat_div.computableIn
    (RelativeComputable.comp (f := CauchyModulus.dyadic)
      CauchyModulus.primrec_dyadic.computableIn ComputableIn.snd) hd

theorem approximation_error (N : EffectiveEvent.Name A S)
    (cs : α → List AffineCode.Data) (a : α) (k : ℕ) :
    |(approximation N cs a k : ℝ) - (StageFiniteProbability.law (cs a)).real (S a)| ≤
      (error cs a k : ℝ) := by
  have hm : MeasurableSet (StageFiniteProbability.event (cs a)) :=
    StageFiniteProbability.measurableSet_event (cs a)
  have hn : (0 : ℝ) ≤ denominator (cs a) := Rat.cast_nonneg.mpr (denominator_nonneg (cs a))
  have he : fairCoin.real ((StageFiniteProbability.event (cs a) ∩ event (N.code a k)) ∆
      (StageFiniteProbability.event (cs a) ∩ S a)) ≤ (1 / 2 : ℝ) ^ k := by
    apply le_trans (measureReal_mono ?_) (N.error a k)
    intro X hX
    simp only [Set.mem_symmDiff, Set.mem_inter_iff] at *
    tauto
  have habs := (abs_measureReal_sub_le_measureReal_symmDiff
    (hm.inter (measurableSet_event _)).nullMeasurableSet
    (hm.inter (N.measurable a)).nullMeasurableSet).trans he
  rw [approximation, probability_eq, real_law, real_law, ← sub_div, abs_div,
    abs_of_nonneg hn]
  simpa only [error, CauchyModulus.dyadic, Rat.cast_div, Rat.cast_pow,
    Rat.cast_one, Rat.cast_ofNat] using div_le_div_of_nonneg_right habs hn

omit [Primcodable α] in
theorem error_tendsto (cs : α → List AffineCode.Data) (a : α) :
    Filter.Tendsto (fun k => (error cs a k : ℝ)) Filter.atTop (𝓝 0) := by
  have h : Filter.Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa only [error, CauchyModulus.dyadic, Rat.cast_div, Rat.cast_pow,
    Rat.cast_one, Rat.cast_ofNat, zero_div] using h.div_const (denominator (cs a) : ℝ)

end Name

end Klr.EffectiveConditionalEvent
