module

public import Klr.PrefixAverage
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Approximating the level-one set of a bounded density

The Lipschitz ramps `max 0 (1 - m * (1 - x))` converge to the indicator of
`{x = 1}` on `x ≤ 1`. Dominated convergence gives L1 convergence for bounded
Borel densities. A Lipschitz bound transfers finite-table approximations
through each fixed ramp, and thresholding a rational table gives an actual
clopen set with controlled symmetric-difference measure.
-/

@[expose] public section

noncomputable section

namespace Klr.HighSetApproximation

open MeasureTheory Filter PoolApproximation
open scoped Topology symmDiff

/-- A continuous ramp concentrating on the level-one set. -/
def ramp (m : ℕ) (x : ℝ) : ℝ := max 0 (1 - (m : ℝ) * (1 - x))

theorem ramp_nonneg (m : ℕ) (x : ℝ) : 0 ≤ ramp m x := le_max_left _ _

theorem ramp_le_one (m : ℕ) {x : ℝ} (hx : x ≤ 1) : ramp m x ≤ 1 := by
  apply max_le (by norm_num)
  have h := mul_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) (sub_nonneg.mpr hx)
  linarith

@[simp] theorem ramp_one (m : ℕ) : ramp m 1 = 1 := by simp [ramp]

theorem measurable_ramp {g : Cantor → ℝ} (hg : Measurable g) (m : ℕ) :
    Measurable (fun X => ramp m (g X)) := by
  unfold ramp
  fun_prop

theorem integrable_ramp {g : Cantor → ℝ} (hg : Integrable g fairCoin) (m : ℕ) :
    Integrable (fun X => ramp m (g X)) fairCoin := by
  exact (integrable_const 0).sup
    ((integrable_const 1).sub (((integrable_const 1).sub hg).const_mul (m : ℝ)))

/-- The ramp has Lipschitz constant `m`, including the case `m = 0`. -/
theorem norm_ramp_sub_le (m : ℕ) (x y : ℝ) :
    ‖ramp m x - ramp m y‖ ≤ (m : ℝ) * ‖x - y‖ := by
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have h := abs_max_sub_max_le_abs (1 - (m : ℝ) * (1 - x))
    (1 - (m : ℝ) * (1 - y)) 0
  have he : (1 - (m : ℝ) * (1 - x)) - (1 - (m : ℝ) * (1 - y)) =
      (m : ℝ) * (x - y) := by ring
  change |max 0 (1 - (m : ℝ) * (1 - x)) - max 0 (1 - (m : ℝ) * (1 - y))| ≤ _
  rw [max_comm 0 (1 - (m : ℝ) * (1 - x)), max_comm 0 (1 - (m : ℝ) * (1 - y))]
  rw [he, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ m from Nat.cast_nonneg m)] at h
  exact h

/-- On a value strictly below one, sufficiently steep ramps vanish exactly. -/
theorem eventually_ramp_eq_zero {x : ℝ} (hx : x < 1) :
    ∀ᶠ m : ℕ in atTop, ramp m x = 0 := by
  have hpos : 0 < 1 - x := sub_pos.mpr hx
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (1 - x))
  have hN' : (1 : ℝ) < N * (1 - x) := (div_lt_iff₀ hpos).mp hN
  filter_upwards [eventually_ge_atTop N] with m hm
  have hm' : (N : ℝ) ≤ m := by exact_mod_cast hm
  apply max_eq_left
  nlinarith

/-- The Borel level-one set, represented by its real-valued indicator. -/
def highIndicator (g : Cantor → ℝ) : Cantor → ℝ :=
  {X | g X = 1}.indicator (fun _ => 1)

theorem measurable_highIndicator {g : Cantor → ℝ} (hg : Measurable g) :
    Measurable (highIndicator g) :=
  measurable_const.indicator (measurableSet_eq_fun hg measurable_const)

theorem integrable_highIndicator {g : Cantor → ℝ} (hg : Measurable g) :
    Integrable (highIndicator g) fairCoin :=
  (integrable_const 1).indicator (measurableSet_eq_fun hg measurable_const)

theorem tendsto_ramp {g : Cantor → ℝ} (hg1 : ∀ X, g X ≤ 1) (X : Cantor) :
    Tendsto (fun m => ramp m (g X)) atTop (𝓝 (highIndicator g X)) := by
  by_cases hX : g X = 1
  · simpa only [hX, ramp_one, highIndicator, Set.indicator_of_mem
      (show X ∈ {X | g X = 1} from hX)] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  · have hev := eventually_ramp_eq_zero (lt_of_le_of_ne (hg1 X) hX)
    have ht : Tendsto (fun m => ramp m (g X)) atTop (𝓝 0) :=
      tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm)
    simpa only [highIndicator, Set.indicator_of_notMem
      (show X ∉ {X | g X = 1} from hX)] using ht

/-- The pointwise errors are uniformly bounded by one. -/
theorem norm_ramp_sub_high_le_one {g : Cantor → ℝ} (hg1 : ∀ X, g X ≤ 1)
    (m : ℕ) (X : Cantor) : ‖ramp m (g X) - highIndicator g X‖ ≤ 1 := by
  by_cases hX : g X = 1
  · simp [highIndicator, hX]
  · simp only [highIndicator, Set.indicator_of_notMem
      (show X ∉ {X | g X = 1} from hX), sub_zero, Real.norm_eq_abs,
      abs_of_nonneg (ramp_nonneg m (g X))]
    exact ramp_le_one m (hg1 X)

/-- The ramps converge in L1 to the actual high-set indicator. -/
theorem tendsto_integral_norm_ramp_sub_high {g : Cantor → ℝ}
    (hgm : Measurable g) (hg1 : ∀ X, g X ≤ 1) :
    Tendsto (fun m => ∫ X, ‖ramp m (g X) - highIndicator g X‖ ∂fairCoin)
      atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := fairCoin)
    (F := fun m X => ‖ramp m (g X) - highIndicator g X‖)
    (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
    (fun m => ((measurable_ramp hgm m).sub
      (measurable_highIndicator hgm)).norm.aestronglyMeasurable)
    (integrable_const 1)
    (fun m => Eventually.of_forall fun X => by
      simpa only [norm_norm] using norm_ramp_sub_high_le_one hg1 m X)
    (Eventually.of_forall fun X => by
      simpa only [sub_self, norm_zero] using ((tendsto_ramp hg1 X).sub_const
        (highIndicator g X)).norm)
  simpa only [integral_zero] using h

/-- Applying a fixed ramp multiplies L1 error by at most its slope. -/
theorem integral_norm_ramp_sub_le {f g : Cantor → ℝ}
    (hf : Integrable f fairCoin) (hg : Integrable g fairCoin) (m : ℕ) :
    (∫ X, ‖ramp m (f X) - ramp m (g X)‖ ∂fairCoin) ≤
      (m : ℝ) * ∫ X, ‖f X - g X‖ ∂fairCoin := by
  calc
    _ ≤ ∫ X, (m : ℝ) * ‖f X - g X‖ ∂fairCoin :=
      integral_mono ((integrable_ramp hf m).sub (integrable_ramp hg m)).norm
        ((hf.sub hg).norm.const_mul (m : ℝ)) (fun X => norm_ramp_sub_le m (f X) (g X))
    _ = _ := integral_const_mul _ _

/-- Finite approximants can be substituted in the ramps with an explicit error budget. -/
theorem integral_norm_ramp_sub_high_le {f g : Cantor → ℝ}
    (hf : Integrable f fairCoin) (hgm : Measurable g) (hg : Integrable g fairCoin) (m : ℕ) :
    (∫ X, ‖ramp m (f X) - highIndicator g X‖ ∂fairCoin) ≤
      (m : ℝ) * (∫ X, ‖f X - g X‖ ∂fairCoin) +
        ∫ X, ‖ramp m (g X) - highIndicator g X‖ ∂fairCoin := by
  have htri := integral_norm_sub_triangle (integrable_ramp hf m) (integrable_ramp hg m)
    (integrable_highIndicator hgm)
  have hbound := integral_norm_ramp_sub_le hf hg m
  linarith

/-- Threshold a rational prefix table at one half. -/
def threshold {d : ℕ} (table : (Fin d → Bool) → ℚ) : (Fin d → Bool) → Bool :=
  fun u => decide ((1 / 2 : ℚ) < table u)

/-- Thresholding an L1 approximation to an indicator controls symmetric difference. -/
theorem measureReal_symmDiff_threshold_le {H : Set Cantor} (hH : MeasurableSet H)
    {d : ℕ} (table : (Fin d → Bool) → ℚ) :
    fairCoin.real (event (threshold table) ∆ H) ≤
      2 * ∫ X, ‖((eval table X : ℚ) : ℝ) - H.indicator (fun _ => (1 : ℝ)) X‖ ∂fairCoin := by
  classical
  have he : (∫ X, ‖(event (threshold table)).indicator (fun _ => (1 : ℝ)) X -
      H.indicator (fun _ => (1 : ℝ)) X‖ ∂fairCoin) =
      fairCoin.real (event (threshold table) ∆ H) := by
    simpa only [norm_one, mul_one] using
      integral_norm_indicator_sub_indicator (measurableSet_event (threshold table)) hH (1 : ℝ)
  rw [← he]
  have hpoint (X : Cantor) :
      ‖(event (threshold table)).indicator (fun _ => (1 : ℝ)) X -
        H.indicator (fun _ => (1 : ℝ)) X‖ ≤
      2 * ‖((eval table X : ℚ) : ℝ) - H.indicator (fun _ => (1 : ℝ)) X‖ := by
    have hmem : X ∈ event (threshold table) ↔ (1 / 2 : ℚ) < eval table X := by
      simp [event, eval, threshold]
    by_cases hX : X ∈ H <;> by_cases hq : (1 / 2 : ℚ) < eval table X
    · simp [Set.indicator, hmem.mpr hq, hX]
    · have hqr : ((eval table X : ℚ) : ℝ) ≤ 1 / 2 := by
        have hh : ((eval table X : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) :=
          Rat.cast_le.mpr (le_of_not_gt hq)
        norm_num at hh ⊢
        exact hh
      simp only [Set.indicator_of_notMem (mt hmem.mp hq), Set.indicator_of_mem hX,
        zero_sub, norm_neg, norm_one, Real.norm_eq_abs]
      linarith [neg_le_abs (((eval table X : ℚ) : ℝ) - 1)]
    · have hqr : (1 / 2 : ℝ) < ((eval table X : ℚ) : ℝ) := by
        have hh : ((1 / 2 : ℚ) : ℝ) < ((eval table X : ℚ) : ℝ) := Rat.cast_lt.mpr hq
        norm_num at hh ⊢
        exact hh
      simp only [Set.indicator_of_mem (hmem.mpr hq), Set.indicator_of_notMem hX,
        sub_zero, norm_one, Real.norm_eq_abs]
      linarith [le_abs_self ((eval table X : ℚ) : ℝ)]
    · simp [Set.indicator, mt hmem.mp hq, hX]
  calc
    _ ≤ ∫ X, 2 * ‖((eval table X : ℚ) : ℝ) - H.indicator (fun _ => (1 : ℝ)) X‖ ∂fairCoin := by
      apply integral_mono
        (((integrable_const 1).indicator (measurableSet_event (threshold table))).sub
          ((integrable_const 1).indicator hH)).norm
        ((((integrable_eval (fun u => (table u : ℝ))).sub
          ((integrable_const 1).indicator hH)).norm).const_mul 2)
      exact hpoint
    _ = _ := integral_const_mul _ _

/-- The ramp of a rational prefix table is again a rational prefix table. -/
def rampTable {d : ℕ} (m : ℕ) (table : (Fin d → Bool) → ℚ) :
    (Fin d → Bool) → ℚ :=
  fun u => max 0 (1 - (m : ℚ) * (1 - table u))

theorem cast_eval_rampTable {d : ℕ} (m : ℕ) (table : (Fin d → Bool) → ℚ) (X : Cantor) :
    ((eval (rampTable m table) X : ℚ) : ℝ) = ramp m ((eval table X : ℚ) : ℝ) := by
  simp [eval, rampTable, ramp]

/-- A sequence of sufficiently accurate density approximants can be ramped
at increasing slopes while still converging in L1 to the high-set indicator. -/
theorem tendsto_integral_norm_approx_ramp_sub_high {F : ℕ → Cantor → ℝ}
    {g : Cantor → ℝ} (hF : ∀ m, Integrable (F m) fairCoin)
    (hgm : Measurable g) (hg : Integrable g fairCoin) (hg1 : ∀ X, g X ≤ 1)
    (herr : Tendsto (fun m : ℕ => (m : ℝ) * ∫ X, ‖F m X - g X‖ ∂fairCoin) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ X, ‖ramp m (F m X) - highIndicator g X‖ ∂fairCoin)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun m => integral_nonneg fun X => norm_nonneg _)
    (fun m => integral_norm_ramp_sub_high_le (hF m) hgm hg m)
  simpa only [add_zero] using herr.add (tendsto_integral_norm_ramp_sub_high hgm hg1)

/-- Converging rational-table approximations to an indicator yield clopen
approximations converging in symmetric-difference measure. -/
theorem tendsto_measureReal_symmDiff_threshold {H : Set Cantor} (hH : MeasurableSet H)
    (d : ℕ → ℕ) (table : (m : ℕ) → (Fin (d m) → Bool) → ℚ)
    (herr : Tendsto (fun m => ∫ X,
      ‖((eval (table m) X : ℚ) : ℝ) - H.indicator (fun _ => (1 : ℝ)) X‖ ∂fairCoin)
      atTop (𝓝 0)) :
    Tendsto (fun m => fairCoin.real (event (threshold (table m)) ∆ H)) atTop (𝓝 0) := by
  apply squeeze_zero (fun m => measureReal_nonneg)
    (fun m => measureReal_symmDiff_threshold_le hH (table m))
  simpa only [mul_zero] using herr.const_mul 2

end Klr.HighSetApproximation
