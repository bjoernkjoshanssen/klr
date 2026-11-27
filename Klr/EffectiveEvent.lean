module

public import Klr.RationalPrefixCode
public import Klr.Computability.CauchyModulus
public import Klr.StageFiniteProbability

/-!
# Oracle names for measurable events

An event name consists of actual finite rational prefix codes whose threshold
events approximate the given set in symmetric-difference measure. Boolean
operations and integration preserve the oracle. A convergent computable
sequence of clopen events acquires a fast name in one jump.
-/

@[expose] public section

namespace Klr.EffectiveEvent

open MeasureTheory Filter RationalPrefixCode
open _root_.Klr.Computability
open scoped Topology symmDiff

local instance : Encodable ℚ := (inferInstance : Primcodable ℚ).toEncodable

variable {α β : Type*} [Primcodable α] [Primcodable β]

/-- Uniform clopen approximation in measure, with its actual oracle computation. -/
structure Name (A : Oracle) (S : α → Set Cantor) where
  code : α → ℕ → Code
  computable : ComputableIn₂ {oracleFunction A} code
  measurable : ∀ a, MeasurableSet (S a)
  error : ∀ a k, fairCoin.real (event (code a k) ∆ S a) ≤ (1 / 2 : ℝ) ^ k

namespace Name

variable {A B : Oracle} {S T : α → Set Cantor}

/-- Reindexing a uniform family costs no additional oracle. -/
def reindex (N : Name A S) {f : β → α} (hf : ComputableIn {oracleFunction A} f) :
    Name A (fun b => S (f b)) where
  code b k := N.code (f b) k
  computable := RelativeComputable.comp₂ N.computable
    (RelativeComputable.comp hf ComputableIn.fst) ComputableIn.snd
  measurable b := N.measurable (f b)
  error b k := N.error (f b) k

def transfer (N : Name A S) (hAB : Reduces A B) : Name B S where
  code := N.code
  computable := RelativeComputable.transfer N.computable hAB
  measurable := N.measurable
  error := N.error

def compl (N : Name A S) : Name A (fun a => (S a)ᶜ) where
  code a k := RationalPrefixCode.compl (N.code a k)
  computable := RelativeComputable.comp computable_compl.computableIn N.computable
  measurable a := (N.measurable a).compl
  error a k := by
    simpa only [event_compl, compl_symmDiff_compl] using N.error a k

private theorem inter_error (E F S T : Set Cantor) :
    fairCoin.real ((E ∩ F) ∆ (S ∩ T)) ≤
      fairCoin.real (E ∆ S) + fairCoin.real (F ∆ T) := by
  have hs : (E ∩ F) ∆ (S ∩ T) ⊆ (E ∆ S) ∪ (F ∆ T) := by
    intro X hX
    simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_union] at *
    tauto
  exact (measureReal_mono hs).trans (measureReal_union_le _ _)

/-- Each input is requested at one extra bit of accuracy. -/
def inter (N : Name A S) (M : Name A T) : Name A (fun a => S a ∩ T a) where
  code a k := RationalPrefixCode.inter (N.code a (k + 1)) (M.code a (k + 1))
  computable := by
    have hk : ComputableIn {oracleFunction A} (fun p : α × ℕ => p.2 + 1) :=
      (Primrec.succ.comp Primrec.snd).computableIn
    exact RelativeComputable.comp₂ computable_inter.computableIn
      (RelativeComputable.comp₂ N.computable ComputableIn.fst hk)
      (RelativeComputable.comp₂ M.computable ComputableIn.fst hk)
  measurable a := (N.measurable a).inter (M.measurable a)
  error a k := by
    rw [event_inter]
    calc
      _ ≤ fairCoin.real (event (N.code a (k + 1)) ∆ S a) +
          fairCoin.real (event (M.code a (k + 1)) ∆ T a) := inter_error _ _ _ _
      _ ≤ (1 / 2 : ℝ) ^ (k + 1) + (1 / 2 : ℝ) ^ (k + 1) :=
        add_le_add (N.error a (k + 1)) (M.error a (k + 1))
      _ = (1 / 2 : ℝ) ^ k := by rw [pow_succ]; ring

def union (N : Name A S) (M : Name A T) : Name A (fun a => S a ∪ T a) := by
  simpa only [Set.compl_inter, compl_compl] using (N.compl.inter M.compl).compl

/-- A computable finite case distinction selects an event name uniformly. -/
def select (N : Name A S) (M : Name A T) (p : α → Bool)
    (hp : ComputableIn {oracleFunction A} p) :
    Name A (fun a => if p a then S a else T a) where
  code a k := if p a then N.code a k else M.code a k
  computable := by
    have hs : Primrec (fun q : Bool × Code × Code => bif q.1 then q.2.1 else q.2.2) :=
      Primrec.cond Primrec.fst (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
    have hc := RelativeComputable.comp (f := fun q : Bool × Code × Code =>
      bif q.1 then q.2.1 else q.2.2) hs.computableIn
      (RelativeComputable.pair (RelativeComputable.comp hp ComputableIn.fst)
        (RelativeComputable.pair N.computable M.computable))
    exact RelativeComputable.of_eq hc fun q => by simp only [Bool.cond_eq_ite]
  measurable a := by
    cases h : p a
    · simpa only [h, Bool.false_eq_true, ite_false] using M.measurable a
    · simpa only [h, ite_true] using N.measurable a
  error a k := by
    cases h : p a
    · simpa only [h, Bool.false_eq_true, ite_false] using M.error a k
    · simpa only [h, ite_true] using N.error a k

end Name

/-- Replace a table by the exact zero-one indicator of its threshold event. -/
def indicatorCode (c : Code) : Code := RationalPrefixCode.compl (RationalPrefixCode.compl c)

theorem computable_indicatorCode : Computable indicatorCode :=
  computable_compl.comp computable_compl

@[simp] theorem event_indicatorCode (c : Code) : event (indicatorCode c) = event c := by
  simp [indicatorCode]

theorem eval_indicatorCode (c : Code) (X : Cantor) :
    (eval (indicatorCode c) X : ℝ) = (event c).indicator (fun _ => (1 : ℝ)) X := by
  classical
  simp only [indicatorCode, RationalPrefixCode.compl, eval_map, event,
    Set.indicator_apply, Set.mem_ofPred_eq]
  split_ifs <;> norm_num at *

/-- The exact fair-coin probability of a finite coded event. -/
def probability (c : Code) : ℚ :=
  PoolAdvice.average c.1 (fun s => if (1 / 2 : ℚ) < value c s then 1 else 0)

theorem computable_probability : Computable probability := by
  have hpred : PrimrecPred (fun p : Code × List Bool => ¬value p.1 p.2 ≤ 1 / 2) :=
    (RationalComputability.primrec_rat_le.comp primrec_value (Primrec.const (1 / 2))).not
  have hval := (Primrec.ite hpred (Primrec.const (1 : ℚ)) (Primrec.const 0)).to_comp
  apply PoolAdvice.computable_average Computable.fst
  exact hval.of_eq fun p => by simp

theorem probability_eq_measureReal (c : Code) :
    (probability c : ℝ) = fairCoin.real (event c) := by
  classical
  rw [probability, PoolAdvice.average_eq_integral,
    ← integral_indicator_one (measurableSet_event c)]
  apply integral_congr_ae
  filter_upwards [] with X
  simp only [event, eval, Set.indicator_apply, Set.mem_ofPred_eq]
  split_ifs <;> norm_num

namespace Name

variable {A : Oracle} {S : α → Set Cantor}

def probabilityApproximation (N : Name A S) (a : α) (k : ℕ) : ℚ :=
  probability (N.code a k)

theorem probabilityApproximation_computable (N : Name A S) :
    ComputableIn₂ {oracleFunction A} N.probabilityApproximation :=
  RelativeComputable.comp computable_probability.computableIn N.computable

theorem probabilityApproximation_error (N : Name A S) (a : α) (k : ℕ) :
    |(N.probabilityApproximation a k : ℝ) - fairCoin.real (S a)| ≤ (1 / 2 : ℝ) ^ k := by
  rw [probabilityApproximation, probability_eq_measureReal]
  exact (abs_measureReal_sub_le_measureReal_symmDiff
    (measurableSet_event _).nullMeasurableSet (N.measurable a).nullMeasurableSet).trans
      (N.error a k)

end Name

/-- A uniformly computable clopen family has an exact, constant event name. -/
def ofClopen {A : Oracle} {c : α → Code}
    (hc : ComputableIn {oracleFunction A} c) : Name A (fun a => event (c a)) where
  code a _ := c a
  computable := RelativeComputable.comp hc ComputableIn.fst
  measurable a := measurableSet_event (c a)
  error a k := by simp

noncomputable section

private def indicatorL1 (S : Set Cantor) (hS : MeasurableSet S) : Lp ℝ 1 fairCoin :=
  ((integrable_const (1 : ℝ)).indicator hS).toL1 (S.indicator (fun _ => (1 : ℝ)))

private theorem dist_indicatorL1 (c : Code) (S : Set Cantor) (hS : MeasurableSet S) :
    dist (toL1 (indicatorCode c)) (indicatorL1 S hS) = fairCoin.real (event c ∆ S) := by
  rw [toL1, indicatorL1, dist_toL1_eq_integral]
  simp_rw [eval_indicatorCode]
  simpa only [norm_one, mul_one] using
    PoolApproximation.integral_norm_indicator_sub_indicator (measurableSet_event c) hS (1 : ℝ)

/-- Arbitrary convergence in measure of actual clopen codes can be accelerated
in one jump. The input is the program for the codes, not a supplied convergence
modulus. -/
theorem exists_name_of_convergent [Inhabited α] {A : Oracle}
    {S : α → Set Cantor} (hS : ∀ a, MeasurableSet (S a)) {c : α → ℕ → Code}
    (hc : ComputableIn₂ {oracleFunction A} c)
    (hlim : ∀ a, Tendsto (fun n => fairCoin.real (event (c a n) ∆ S a)) atTop (𝓝 0)) :
    Nonempty (Name (OracleJump.jump A) S) := by
  let dec : ℕ → α := RelativeComputable.decodeDefault
  have hdec : Primrec dec := RelativeComputable.primrec_decodeDefault
  let C : ℕ → ℕ → Code := fun i n => indicatorCode (c (dec i) n)
  have hC : ComputableIn₂ {oracleFunction A} C :=
    RelativeComputable.comp computable_indicatorCode.computableIn
      (RelativeComputable.comp₂ hc
        (RelativeComputable.comp hdec.computableIn ComputableIn.fst) ComputableIn.snd)
  let d : ℕ → ℕ → ℕ → ℚ := fun i s t => RationalPrefixCode.distance (C i s) (C i t)
  have hd : ComputableIn {oracleFunction A}
      (fun p : ℕ × (ℕ × ℕ) => d p.1 p.2.1 p.2.2) := by
    have hs : ComputableIn {oracleFunction A}
        (fun p : ℕ × (ℕ × ℕ) => C p.1 p.2.1) :=
      RelativeComputable.comp (f := fun p : ℕ × ℕ => C p.1 p.2)
        (g := fun p : ℕ × (ℕ × ℕ) => (p.1, p.2.1)) hC
        (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)).computableIn
    have ht : ComputableIn {oracleFunction A}
        (fun p : ℕ × (ℕ × ℕ) => C p.1 p.2.2) :=
      RelativeComputable.comp (f := fun p : ℕ × ℕ => C p.1 p.2)
        (g := fun p : ℕ × (ℕ × ℕ) => (p.1, p.2.2)) hC
        (Primrec.fst.pair (Primrec.snd.comp Primrec.snd)).computableIn
    exact RelativeComputable.comp₂ (f := RationalPrefixCode.distance)
      RationalPrefixCode.computable_distance.computableIn hs ht
  have hconv (i : ℕ) : Tendsto (fun n => toL1 (C i n)) atTop
      (𝓝 (indicatorL1 (S (dec i)) (hS (dec i)))) := by
    rw [tendsto_iff_dist_tendsto_zero]
    simpa only [C, dist_indicatorL1] using hlim (dec i)
  obtain ⟨m, hm, herr⟩ := CauchyModulus.exists_limit_modulus hd
    (fun i s t => dist_toL1 (C i s) (C i t)) hconv
  refine ⟨{
    code := fun a k => c a (m (Encodable.encode a) k)
    computable := ?_
    measurable := hS
    error := ?_ }⟩
  · exact RelativeComputable.comp₂ (RelativeComputable.jump hc) ComputableIn.fst
      (RelativeComputable.comp₂ hm (Primrec.encode.comp Primrec.fst).computableIn
        ComputableIn.snd)
  · intro a k
    simpa only [C, dec, RelativeComputable.decodeDefault_encode, dist_indicatorL1] using
      herr (Encodable.encode a) k

/-- Increasing clopen approximants to an open event always converge in measure. -/
theorem tendsto_symmDiff_iUnion (c : ℕ → Code) (hc : Monotone (fun n => event (c n))) :
    Tendsto (fun n => fairCoin.real (event (c n) ∆ ⋃ m, event (c m))) atTop (𝓝 0) := by
  have hm := (ENNReal.tendsto_toReal (measure_ne_top fairCoin _)).comp
    (tendsto_measure_iUnion_atTop (μ := fairCoin) hc)
  have he (n : ℕ) :
      fairCoin.real (event (c n) ∆ ⋃ m, event (c m)) =
        fairCoin.real (⋃ m, event (c m)) - fairCoin.real (event (c n)) := by
    rw [symmDiff_of_le (Set.subset_iUnion (fun m => event (c m)) n),
      measureReal_sdiff (Set.subset_iUnion (fun m => event (c m)) n)
        (measurableSet_event (c n))]
  have h : Tendsto (fun n => fairCoin.real (⋃ m, event (c m)) -
      fairCoin.real (event (c n))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, measureReal_def, sub_self] using
      (tendsto_const_nhds (x := fairCoin.real (⋃ m, event (c m)))).sub hm
  simpa only [he] using h

theorem exists_name_iUnion [Inhabited α] {A : Oracle} {c : α → ℕ → Code}
    (hc : ComputableIn₂ {oracleFunction A} c)
    (hmono : ∀ a, Monotone (fun n => event (c a n))) :
    Nonempty (Name (OracleJump.jump A) (fun a => ⋃ n, event (c a n))) :=
  exists_name_of_convergent
    (fun a => MeasurableSet.iUnion (fun n => measurableSet_event (c a n))) hc
    (fun a => tendsto_symmDiff_iUnion (c a) (hmono a))

end

end Klr.EffectiveEvent
