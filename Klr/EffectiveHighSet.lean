module

public import Klr.RationalPrefixCode
public import Klr.Computability.CauchyModulus

/-!
# Two-jump clopen names for level-one sets

Uniform oracle-computable cylinder integrals give a convergent sequence of
rational prefix tables. One jump supplies an L1 modulus. Ramping increasingly
accurate tables then converges to the indicator of the level-one set; one
more jump supplies its L1 modulus. Thresholding gives actual clopen sets
with an explicit error in symmetric-difference measure.
-/

@[expose] public section

namespace Klr.EffectiveHighSet

open MeasureTheory Filter RationalPrefixCode RationalComputability
open Klr.Computability
open scoped Topology symmDiff

local instance : Encodable ℚ := (inferInstance : Primcodable ℚ).toEncodable

private theorem distances_computableIn {A : Oracle} {c : ℕ → ℕ → Code}
    (hc : ComputableIn₂ {oracleFunction A} c) :
    ComputableIn {oracleFunction A}
      (fun p : ℕ × (ℕ × ℕ) => distance (c p.1 p.2.1) (c p.1 p.2.2)) := by
  have hleft : ComputableIn {oracleFunction A}
      (fun p : ℕ × (ℕ × ℕ) => c p.1 p.2.1) :=
    RelativeComputable.comp₂ hc ComputableIn.fst
      (RelativeComputable.comp ComputableIn.fst ComputableIn.snd)
  have hright : ComputableIn {oracleFunction A}
      (fun p : ℕ × (ℕ × ℕ) => c p.1 p.2.2) :=
    RelativeComputable.comp₂ hc ComputableIn.fst
      (RelativeComputable.comp ComputableIn.snd ComputableIn.snd)
  exact RelativeComputable.comp₂ computable_distance.computableIn hleft hright

/-- A computable sequence of rational prefix tables with an ordinary L1
convergence proof has a fast name in one jump. -/
theorem exists_fast_name {A : Oracle} {c : ℕ → ℕ → Code} {g : ℕ → Cantor → ℝ}
    (hc : ComputableIn₂ {oracleFunction A} c)
    (hg : ∀ i, Integrable (g i) fairCoin)
    (hlim : ∀ i, Tendsto
      (fun n => ∫ X, ‖(eval (c i n) X : ℝ) - g i X‖ ∂fairCoin) atTop (𝓝 0)) :
    ∃ f : ℕ → ℕ → Code, ComputableIn₂ {oracleFunction (OracleJump.jump A)} f ∧
      ∀ i k, (∫ X, ‖(eval (f i k) X : ℝ) - g i X‖ ∂fairCoin) ≤ (1 / 2 : ℝ) ^ k := by
  obtain ⟨m, hm, hms⟩ := CauchyModulus.exists_limit_modulus
    (A := A) (d := fun i s t => distance (c i s) (c i t))
    (a := fun i n => toL1 (c i n)) (l := fun i => (hg i).toL1 (g i))
    (distances_computableIn hc)
    (fun i s t => dist_toL1 (c i s) (c i t))
    (fun i => tendsto_toL1 (hg i) (hlim i))
  refine ⟨fun i k => c i (m i k), ?_, fun i k => ?_⟩
  · exact RelativeComputable.comp₂ (RelativeComputable.jump hc) ComputableIn.fst hm
  · simpa only [toL1, dist_toL1_eq_integral] using hms i k

/-- Prefix coefficients obtained from cylinder integrals at twice the depth
have a uniformly vanishing coefficient error. -/
def coefficientCode (C : ℕ → List Bool → ℕ → ℚ) (i d : ℕ) : Code :=
  ofTable d (fun s => (2 : ℚ) ^ d * C i s (d + d))

theorem coefficientCode_computableIn {A : Oracle} {C : ℕ → List Bool → ℕ → ℚ}
    (hC : ComputableIn {oracleFunction A}
      (fun p : ℕ × (List Bool × ℕ) => C p.1 p.2.1 p.2.2)) :
    ComputableIn₂ {oracleFunction A} (coefficientCode C) := by
  change ComputableIn {oracleFunction A}
    (fun p : ℕ × ℕ => ofTable p.2 (fun s => (2 : ℚ) ^ p.2 * C p.1 s (p.2 + p.2)))
  have hp : Primrec (fun n : ℕ => (2 : ℚ) ^ n) :=
    (primrec_rat_natCast.comp
      ((Primrec₂.unpaired'.mp Nat.Primrec.pow).comp (Primrec.const 2) Primrec.id)).of_eq
        fun _ => by simp
  have hd : Primrec (fun p : (ℕ × ℕ) × List Bool => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have harg : Primrec (fun p : (ℕ × ℕ) × List Bool => (p.1.1, (p.2, p.1.2 + p.1.2))) :=
    (Primrec.fst.comp Primrec.fst).pair (Primrec.snd.pair (Primrec.nat_add.comp hd hd))
  have hpow : ComputableIn {oracleFunction A}
      (fun p : (ℕ × ℕ) × List Bool => (2 : ℚ) ^ p.1.2) :=
    (hp.comp hd).computableIn
  have hvalue : ComputableIn {oracleFunction A}
      (fun p : (ℕ × ℕ) × List Bool => C p.1.1 p.2 (p.1.2 + p.1.2)) :=
    RelativeComputable.comp
      (f := fun p : ℕ × (List Bool × ℕ) => C p.1 p.2.1 p.2.2)
      (g := fun p : (ℕ × ℕ) × List Bool => (p.1.1, (p.2, p.1.2 + p.1.2)))
      hC harg.computableIn
  have hv : ComputableIn {oracleFunction A}
      (fun p : (ℕ × ℕ) × List Bool => (2 : ℚ) ^ p.1.2 * C p.1.1 p.2 (p.1.2 + p.1.2)) :=
    RelativeComputable.comp₂ (f := fun a b : ℚ => a * b)
      primrec_rat_mul.computableIn₂ hpow hvalue
  exact computableIn_ofTable (d := fun p : ℕ × ℕ => p.2)
    (q := fun p s => (2 : ℚ) ^ p.2 * C p.1 s (p.2 + p.2)) ComputableIn.snd hv

private theorem two_pow_mul_dyadic_double (d : ℕ) :
    (2 : ℝ) ^ d * (1 / 2 : ℝ) ^ (d + d) = (1 / 2 : ℝ) ^ d := by
  rw [pow_add, ← mul_assoc, ← mul_pow]
  norm_num

theorem coefficientCode_error {C : ℕ → List Bool → ℕ → ℚ} {g : ℕ → Cantor → ℝ}
    (hC : ∀ i s k, ‖(C i s k : ℝ) - ∫ X in cylinder s, g i X ∂fairCoin‖ ≤
      (1 / 2 : ℝ) ^ k) (i d : ℕ) (u : Fin d → Bool) :
    ‖(table (coefficientCode C i d) u : ℝ) - PrefixAverage.averageTable d (g i) u‖ ≤
      (1 / 2 : ℝ) ^ d := by
  change ‖(value (ofTable d (fun s => (2 : ℚ) ^ d * C i s (d + d))) (List.ofFn u) : ℝ) -
    PrefixAverage.averageTable d (g i) u‖ ≤ _
  simp only [value_ofTable _ List.length_ofFn,
    Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, PrefixAverage.averageTable,
    PrefixAverage.fiber_eq_cylinder]
  rw [← mul_sub, norm_mul,
    Real.norm_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) d)]
  calc
    _ ≤ (2 : ℝ) ^ d * (1 / 2 : ℝ) ^ (d + d) :=
      mul_le_mul_of_nonneg_left (hC i (List.ofFn u) (d + d)) (by positivity)
    _ = _ := two_pow_mul_dyadic_double d

theorem coefficientCode_tendsto {C : ℕ → List Bool → ℕ → ℚ} {g : ℕ → Cantor → ℝ}
    (hgm : ∀ i, Measurable (g i)) (hg : ∀ i, Integrable (g i) fairCoin)
    (hC : ∀ i s k, ‖(C i s k : ℝ) - ∫ X in cylinder s, g i X ∂fairCoin‖ ≤
      (1 / 2 : ℝ) ^ k) (i : ℕ) :
    Tendsto (fun d => ∫ X, ‖(eval (coefficientCode C i d) X : ℝ) - g i X‖ ∂fairCoin)
      atTop (𝓝 0) := by
  have ht := PrefixAverage.tendsto_integral_norm_table_sub
    (hgm i) (hg i) (fun d => table (coefficientCode C i d))
    (fun d => (1 / 2 : ℝ) ^ d)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    (coefficientCode_error hC i)
  convert ht using 1
  funext d
  congr 1
  funext X
  exact congrArg (fun q : ℚ => ‖(q : ℝ) - g i X‖)
    (eval_table (coefficientCode C i d) X).symm

/-- Cylinder-integral names determine uniformly fast L1 names with one jump. -/
theorem exists_density_name {A : Oracle} {C : ℕ → List Bool → ℕ → ℚ}
    {g : ℕ → Cantor → ℝ}
    (hC : ComputableIn {oracleFunction A}
      (fun p : ℕ × (List Bool × ℕ) => C p.1 p.2.1 p.2.2))
    (herror : ∀ i s k, ‖(C i s k : ℝ) - ∫ X in cylinder s, g i X ∂fairCoin‖ ≤
      (1 / 2 : ℝ) ^ k)
    (hgm : ∀ i, Measurable (g i)) (hg : ∀ i, Integrable (g i) fairCoin) :
    ∃ f : ℕ → ℕ → Code, ComputableIn₂ {oracleFunction (OracleJump.jump A)} f ∧
      ∀ i k, (∫ X, ‖(eval (f i k) X : ℝ) - g i X‖ ∂fairCoin) ≤ (1 / 2 : ℝ) ^ k :=
  exists_fast_name (coefficientCode_computableIn hC) hg
    (coefficientCode_tendsto hgm hg herror)

/-- Ramping a fast L1 name at precision twice its slope still converges in L1. -/
theorem ramp_name_tendsto {f : ℕ → ℕ → Code} {g : ℕ → Cantor → ℝ}
    (hgm : ∀ i, Measurable (g i)) (hg : ∀ i, Integrable (g i) fairCoin)
    (hg1 : ∀ i X, g i X ≤ 1)
    (hf : ∀ i k, (∫ X, ‖(eval (f i k) X : ℝ) - g i X‖ ∂fairCoin) ≤ (1 / 2 : ℝ) ^ k)
    (i : ℕ) :
    Tendsto (fun m => ∫ X,
      ‖(eval (ramp m (f i (m + m))) X : ℝ) - HighSetApproximation.highIndicator (g i) X‖
      ∂fairCoin) atTop (𝓝 0) := by
  have herr : Tendsto (fun m : ℕ => (m : ℝ) *
      ∫ X, ‖(eval (f i (m + m)) X : ℝ) - g i X‖ ∂fairCoin) atTop (𝓝 0) := by
    apply squeeze_zero (fun m => mul_nonneg (Nat.cast_nonneg m)
      (integral_nonneg fun X => norm_nonneg _)) (fun m => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num))
    calc
      _ ≤ (m : ℝ) * (1 / 2 : ℝ) ^ (m + m) :=
        mul_le_mul_of_nonneg_left (hf i (m + m)) (Nat.cast_nonneg m)
      _ ≤ (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ (m + m) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast (Nat.lt_two_pow_self (n := m)).le
      _ = _ := two_pow_mul_dyadic_double m
  simpa only [cast_eval_ramp] using
    HighSetApproximation.tendsto_integral_norm_approx_ramp_sub_high
      (fun m => integrable_eval (f i (m + m))) (hgm i) (hg i) (hg1 i) herr

/-- The level-one set of a bounded Borel function has a uniform clopen name
in the second jump of its cylinder-integral oracle. -/
theorem exists_highSet_name {A : Oracle} {C : ℕ → List Bool → ℕ → ℚ}
    {g : ℕ → Cantor → ℝ}
    (hC : ComputableIn {oracleFunction A}
      (fun p : ℕ × (List Bool × ℕ) => C p.1 p.2.1 p.2.2))
    (herror : ∀ i s k, ‖(C i s k : ℝ) - ∫ X in cylinder s, g i X ∂fairCoin‖ ≤
      (1 / 2 : ℝ) ^ k)
    (hgm : ∀ i, Measurable (g i))
    (hg0 : ∀ i X, 0 ≤ g i X) (hg1 : ∀ i X, g i X ≤ 1) :
    ∃ h : ℕ → ℕ → Code,
      ComputableIn₂ {oracleFunction (OracleJump.jump (OracleJump.jump A))} h ∧
      ∀ i k, fairCoin.real (event (h i k) ∆ {X | g i X = 1}) ≤ (1 / 2 : ℝ) ^ k := by
  have hg (i : ℕ) : Integrable (g i) fairCoin :=
    Integrable.of_bound (hgm i).aestronglyMeasurable 1
      (Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg0 i X)]
        exact hg1 i X)
  obtain ⟨f, hf, hfs⟩ := exists_density_name hC herror hgm hg
  have hr : ComputableIn₂ {oracleFunction (OracleJump.jump A)}
      (fun i m => ramp m (f i (m + m))) := by
    have hindex : Primrec (fun p : ℕ × ℕ => (p.1, p.2 + p.2)) :=
      Primrec.fst.pair (Primrec.nat_add.comp Primrec.snd Primrec.snd)
    exact RelativeComputable.comp₂ computable_ramp.computableIn ComputableIn.snd
      (RelativeComputable.comp hf hindex.computableIn)
  obtain ⟨h, hh, hhs⟩ := exists_fast_name hr
    (fun i => HighSetApproximation.integrable_highIndicator (hgm i))
    (ramp_name_tendsto hgm hg hg1 hfs)
  refine ⟨fun i k => h i (k + 1), ?_, fun i k => ?_⟩
  · exact RelativeComputable.comp₂ hh ComputableIn.fst
      (Primrec.succ.comp Primrec.snd).computableIn
  · have hb := measureReal_symmDiff_event_le (h i (k + 1)) (H := {X | g i X = 1})
      (measurableSet_eq_fun (hgm i) measurable_const)
    have he := hhs i (k + 1)
    change (∫ X, ‖(eval (h i (k + 1)) X : ℝ) -
      {X | g i X = 1}.indicator (fun _ => (1 : ℝ)) X‖ ∂fairCoin) ≤ _ at he
    calc
      _ ≤ 2 * (1 / 2 : ℝ) ^ (k + 1) := hb.trans (mul_le_mul_of_nonneg_left he (by norm_num))
      _ = (1 / 2 : ℝ) ^ k := by rw [pow_succ]; ring

end Klr.EffectiveHighSet
