module

public import Klr.PoolApproximationFunction
public import Klr.FiniteMeasure

/-!
# Prefix averages from cylinder integrals

Averaging over the finite partition into depth-`d` cylinders is an L1
contraction and fixes every shallower prefix table. Density of those tables
then gives L1 convergence for every integrable Borel function. In particular,
computable cylinder integrals determine a convergent sequence of finite
approximants without requiring an effective Hilbert-space representation.
-/

@[expose] public section

noncomputable section

namespace Klr.PrefixAverage

open MeasureTheory Filter PoolApproximation
open scoped ENNReal BigOperators Topology

/-- One fiber of the depth-`d` prefix map. -/
def fiber (d : ℕ) (u : Fin d → Bool) : Set Cantor := {X | bits d X = u}

/-- Prefix fibers agree with the repository's list-coded cylinders. -/
theorem fiber_eq_cylinder (d : ℕ) (u : Fin d → Bool) :
    fiber d u = cylinder (List.ofFn u) := by
  have hget (i : Fin d) : (List.ofFn u).getD i.val false = u i := by
    rw [List.getD_eq_getElem _ false (by simp)]
    simp
  ext X
  constructor
  · intro h i hi
    have hi' : i < d := by simpa using hi
    rw [hget ⟨i, hi'⟩]
    exact congrFun h ⟨i, hi'⟩
  · intro h
    funext i
    change X i.val = u i
    rw [← hget i]
    exact h i.val (by simp)

theorem measurableSet_fiber (d : ℕ) (u : Fin d → Bool) :
    MeasurableSet (fiber d u) :=
  (measurable_prefix d) (measurableSet_singleton u)

theorem measure_fiber (d : ℕ) (u : Fin d → Bool) :
    fairCoin (fiber d u) = (1 / 2 : ℝ≥0∞) ^ d := by
  change fairCoin {X | bits d X = u} = _
  have hbits : bits d = FiniteMeasure.coordinateBits (fun i : Fin d => i.val) := rfl
  rw [hbits]
  simpa only [Fintype.card_fin] using
    FiniteMeasure.fairCoin_coordinate_singleton (fun i : Fin d => i.val) Fin.val_injective u

theorem measureReal_fiber (d : ℕ) (u : Fin d → Bool) :
    fairCoin.real (fiber d u) = (1 / 2 : ℝ) ^ d := by
  simp [measureReal_def, measure_fiber, ENNReal.toReal_pow]

theorem iUnion_fiber (d : ℕ) : (⋃ u, fiber d u) = Set.univ := by
  ext X
  simp [fiber]

theorem pairwise_disjoint_fiber (d : ℕ) :
    Pairwise (fun u v => Disjoint (fiber d u) (fiber d v)) := by
  intro u v huv
  refine Set.disjoint_left.mpr ?_
  intro X hXu hXv
  exact huv (hXu.symm.trans hXv)

/-- Integration splits over the finite prefix partition. -/
theorem integral_eq_sum_fiber {g : Cantor → ℝ} (hg : Integrable g fairCoin) (d : ℕ) :
    (∫ X, g X ∂fairCoin) = ∑ u, ∫ X in fiber d u, g X ∂fairCoin := by
  simpa only [iUnion_fiber, Measure.restrict_univ] using
    integral_iUnion_fintype (measurableSet_fiber d) (pairwise_disjoint_fiber d)
      (fun _ => hg.integrableOn)

/-- A finite table is constant on each fiber. -/
theorem setIntegral_eval {d : ℕ} (table : (Fin d → Bool) → ℝ) (u : Fin d → Bool) :
    (∫ X in fiber d u, eval table X ∂fairCoin) = (1 / 2 : ℝ) ^ d * table u := by
  calc
    _ = ∫ _X in fiber d u, table u ∂fairCoin :=
      setIntegral_congr_fun (measurableSet_fiber d u) (fun X hX => by
        change table (bits d X) = table u
        rw [hX])
    _ = _ := by simp [measureReal_fiber, smul_eq_mul]

/-- Fair-coin integration of a prefix table is its uniform finite average. -/
theorem integral_eval {d : ℕ} (table : (Fin d → Bool) → ℝ) :
    (∫ X, eval table X ∂fairCoin) = ∑ u, (1 / 2 : ℝ) ^ d * table u := by
  rw [integral_eq_sum_fiber (integrable_eval table) d]
  simp_rw [setIntegral_eval]

/-- The normalized integral of the target over each prefix cylinder. -/
def averageTable (d : ℕ) (g : Cantor → ℝ) (u : Fin d → Bool) : ℝ :=
  (2 : ℝ) ^ d * ∫ X in fiber d u, g X ∂fairCoin

/-- The depth-`d` average as a function on Cantor space. -/
def average (d : ℕ) (g : Cantor → ℝ) : Cantor → ℝ := eval (averageTable d g)

theorem measurable_average (d : ℕ) (g : Cantor → ℝ) : Measurable (average d g) :=
  measurable_eval _

theorem integrable_average (d : ℕ) (g : Cantor → ℝ) : Integrable (average d g) fairCoin :=
  integrable_eval _

theorem mass_mul_two_pow (d : ℕ) : (1 / 2 : ℝ) ^ d * (2 : ℝ) ^ d = 1 := by
  rw [← mul_pow]
  norm_num

theorem averageTable_nonneg {g : Cantor → ℝ} (hg : ∀ X, 0 ≤ g X)
    (d : ℕ) (u : Fin d → Bool) : 0 ≤ averageTable d g u :=
  mul_nonneg (by positivity) (integral_nonneg hg)

theorem averageTable_le_one {g : Cantor → ℝ} (hg : Integrable g fairCoin)
    (hg1 : ∀ X, g X ≤ 1) (d : ℕ) (u : Fin d → Bool) : averageTable d g u ≤ 1 := by
  calc
    _ ≤ (2 : ℝ) ^ d * ∫ _X in fiber d u, (1 : ℝ) ∂fairCoin :=
      mul_le_mul_of_nonneg_left (integral_mono hg.integrableOn (integrable_const 1) hg1)
        (by positivity)
    _ = 1 := by simp [measureReal_fiber, mul_comm]

/-- Prefix averaging fixes a table at its own depth. -/
theorem average_eval {d : ℕ} (table : (Fin d → Bool) → ℝ) :
    average d (eval table) = eval table := by
  funext X
  change (2 : ℝ) ^ d * (∫ Y in fiber d (bits d X), eval table Y ∂fairCoin) = _
  rw [setIntegral_eval, ← mul_assoc, mul_comm ((2 : ℝ) ^ d), mass_mul_two_pow, one_mul]
  rfl

/-- Averaging at any later depth also fixes a finite-prefix table. -/
theorem average_eval_of_le {d e : ℕ} (hde : d ≤ e) (table : (Fin d → Bool) → ℝ) :
    average e (eval table) = eval table := by
  have he : eval (liftTable hde table) = eval table := funext (eval_liftTable hde table)
  simpa only [he] using average_eval (liftTable hde table)

theorem average_sub {f g : Cantor → ℝ} (hf : Integrable f fairCoin)
    (hg : Integrable g fairCoin) (d : ℕ) :
    average d (fun X => f X - g X) = fun X => average d f X - average d g X := by
  funext X
  simp only [average, eval, averageTable, integral_sub hf.integrableOn hg.integrableOn,
    mul_sub]

/-- Prefix averaging contracts the integral of the absolute value. -/
theorem integral_norm_average_le {g : Cantor → ℝ} (hg : Integrable g fairCoin) (d : ℕ) :
    (∫ X, ‖average d g X‖ ∂fairCoin) ≤ ∫ X, ‖g X‖ ∂fairCoin := by
  change (∫ X, eval (fun u => ‖averageTable d g u‖) X ∂fairCoin) ≤ _
  rw [integral_eval, integral_eq_sum_fiber hg.norm d]
  apply Finset.sum_le_sum
  intro u _
  calc
    (1 / 2 : ℝ) ^ d * ‖averageTable d g u‖ =
        ‖∫ X in fiber d u, g X ∂fairCoin‖ := by
      rw [averageTable, norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ d),
        ← mul_assoc, mass_mul_two_pow, one_mul]
    _ ≤ _ := norm_integral_le_integral_norm _

/-- The prefix-average operator is an L1 contraction. -/
theorem integral_norm_average_sub_le {f g : Cantor → ℝ}
    (hf : Integrable f fairCoin) (hg : Integrable g fairCoin) (d : ℕ) :
    (∫ X, ‖average d f X - average d g X‖ ∂fairCoin) ≤ ∫ X, ‖f X - g X‖ ∂fairCoin := by
  have h := integral_norm_average_le (hf.sub hg) d
  change (∫ X, ‖average d (fun X => f X - g X) X‖ ∂fairCoin) ≤
    ∫ X, ‖f X - g X‖ ∂fairCoin at h
  rw [average_sub hf hg] at h
  exact h

/-- Density and contraction give convergence, without a convergence modulus. -/
theorem eventually_integral_norm_sub_lt {g : Cantor → ℝ}
    (hgm : Measurable g) (hg : Integrable g fairCoin) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ d in atTop, (∫ X, ‖average d g X - g X‖ ∂fairCoin) < ε := by
  obtain ⟨d, table, htable⟩ := exists_realTable_integral_norm_sub_lt hgm hg (half_pos hε)
  filter_upwards [eventually_ge_atTop d] with e hde
  have hcontract := integral_norm_average_sub_le hg (integrable_eval table) e
  rw [average_eval_of_le hde table] at hcontract
  have htri := integral_norm_sub_triangle (integrable_average e g) (integrable_eval table) hg
  have heq : (∫ X, ‖g X - eval table X‖ ∂fairCoin) =
      ∫ X, ‖eval table X - g X‖ ∂fairCoin := by simp only [norm_sub_rev]
  rw [heq] at hcontract
  linarith

/-- The explicit prefix averages converge to every integrable Borel target in L1. -/
theorem tendsto_integral_norm_sub {g : Cantor → ℝ}
    (hgm : Measurable g) (hg : Integrable g fairCoin) :
    Tendsto (fun d => ∫ X, ‖average d g X - g X‖ ∂fairCoin) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    exact Eventually.of_forall fun d => hb.trans_le (integral_nonneg fun X => norm_nonneg _)
  · intro b hb
    exact eventually_integral_norm_sub_lt hgm hg hb

/-- Uniform rational approximation of the coefficient table transfers to L1. -/
theorem integral_norm_table_sub_le {g : Cantor → ℝ} (hg : Integrable g fairCoin)
    {d : ℕ} (table : (Fin d → Bool) → ℚ) {δ : ℝ}
    (hδ : ∀ u, ‖(table u : ℝ) - averageTable d g u‖ ≤ δ) :
    (∫ X, ‖((eval table X : ℚ) : ℝ) - g X‖ ∂fairCoin) ≤
      δ + ∫ X, ‖average d g X - g X‖ ∂fairCoin := by
  have htable := integrable_eval (fun u => (table u : ℝ))
  have hbound : (∫ X, ‖((eval table X : ℚ) : ℝ) - average d g X‖ ∂fairCoin) ≤ δ := by
    calc
      _ ≤ ∫ _X : Cantor, δ ∂fairCoin :=
        integral_mono (htable.sub (integrable_average d g)).norm (integrable_const δ)
          (fun X => hδ (bits d X))
      _ = δ := by simp
  have htri := integral_norm_sub_triangle htable (integrable_average d g) hg
  simp only [eval] at htri hbound ⊢
  linarith

/-- Rational coefficient approximations with vanishing uniform error converge in L1. -/
theorem tendsto_integral_norm_table_sub {g : Cantor → ℝ}
    (hgm : Measurable g) (hg : Integrable g fairCoin)
    (table : (d : ℕ) → (Fin d → Bool) → ℚ) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0))
    (happrox : ∀ d u, ‖(table d u : ℝ) - averageTable d g u‖ ≤ δ d) :
    Tendsto (fun d => ∫ X, ‖((eval (table d) X : ℚ) : ℝ) - g X‖ ∂fairCoin)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun d => integral_nonneg fun X => norm_nonneg _)
    (fun d => integral_norm_table_sub_le hg (table d) (happrox d))
  simpa only [add_zero] using hδ.add (tendsto_integral_norm_sub hgm hg)

end Klr.PrefixAverage
