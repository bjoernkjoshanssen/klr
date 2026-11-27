module

public import Klr.LeftCeReservoir
public import Klr.UniformStrategyFamily
public import Klr.PoolWeighted
public import Klr.PoolAdviceComputable
public import Klr.PoolAdviceMeasure

/-!
# Ordinary left-c.e. names for query coordinates

Cylinder integrals of eventual query indicators have increasing, exactly
computable rational finite-horizon approximations. The normalized weighted
query probability has the same property by simultaneously truncating the
strategy index and the query horizon. Together these give one `LowerName`
for all scalar coordinates used by the effective reservoir construction.
-/

@[expose] public section

namespace Klr.EffectiveQueryCoordinates

open MeasureTheory Filter RationalComputability
open scoped Topology BigOperators

/-- Finite querying on prescribed answer strings. -/
def reads (π : ℕ → ScanRule) (i a V : ℕ) (v : List Bool) : Bool :=
  (List.range V).any fun t => decide ((π i).query (v.take t) = a)

theorem reads_prefix (π : ℕ → ScanRule) (i a V n : ℕ) (hV : V ≤ n) (Z : Cantor) :
    reads π i a V (ScanRule.inputPrefix Z n) = true ↔ PoolQuery.ReadsBy (π i) a V Z := by
  simp only [reads, List.any_eq_true, List.mem_range, decide_eq_true_eq,
    PoolQuery.ReadsBy, PoolQuery.queryAt]
  constructor <;> rintro ⟨t, ht, h⟩ <;> refine ⟨t, ht, ?_⟩
  · simpa only [PoolAdvice.inputPrefix_take Z (ht.le.trans hV)] using h
  · simpa only [PoolAdvice.inputPrefix_take Z (ht.le.trans hV)] using h

theorem computable_reads (π : ℕ → ScanRule)
    (hπ : Computable (fun p : ℕ × List Bool => (π p.1).query p.2))
    {α : Type*} [Primcodable α] {i a V : α → ℕ} {v : α → List Bool}
    (hi : Computable i) (ha : Computable a) (hV : Computable V) (hv : Computable v) :
    Computable (fun x => reads π (i x) (a x) (V x) (v x)) := by
  have hp := Primrec.list_take.to_comp.comp Computable.snd (hv.comp Computable.fst)
  have hq := hπ.comp ((hi.comp Computable.fst).pair hp)
  have he := Primrec.eq.decide.to_comp.comp hq (ha.comp Computable.fst)
  exact SparseSearch.computable_list_any
    (p := fun x t => decide ((π (i x)).query ((v x).take t) = a x))
    (Primrec.list_range.to_comp.comp hV) he

/-- The cylinder coordinate of the eventual query indicator. -/
noncomputable def cylinderCoordinate (π : ℕ → ScanRule) (i : ℕ) (σ : List Bool)
    (a : ℕ) : ℝ :=
  ∫ Z in cylinder σ, PoolQuery.indicator (π i) a Z ∂fairCoin

/-- Exact finite-horizon cylinder mass, computed by a finite rational average. -/
def cylinderApprox (π : ℕ → ScanRule) (i : ℕ) (σ : List Bool) (a V : ℕ) : ℚ :=
  PoolAdvice.average (max V σ.length) fun v =>
    if v.take σ.length = σ then if reads π i a V v then 1 else 0 else 0

theorem cylinderApprox_eq_integral (π : ℕ → ScanRule) (i : ℕ) (σ : List Bool)
    (a V : ℕ) :
    (cylinderApprox π i σ a V : ℝ) =
      ∫ Z in cylinder σ, PoolQuery.indicatorBy (π i) a V Z ∂fairCoin := by
  rw [cylinderApprox, PoolAdvice.average_eq_integral,
    ← integral_indicator (measurableSet_cylinder σ)]
  apply integral_congr_ae
  filter_upwards [] with Z
  have hp := PoolAdvice.inputPrefix_take Z (Nat.le_max_right V σ.length)
  have hc := PoolAdvice.inputPrefix_eq_iff_mem_cylinder Z σ.length σ rfl
  have hr := reads_prefix π i a V (max V σ.length) (Nat.le_max_left _ _) Z
  by_cases hZ : Z ∈ cylinder σ <;> by_cases hR : PoolQuery.ReadsBy (π i) a V Z
  all_goals simp [hp, hc, hr, hZ, hR, PoolQuery.indicatorBy]

theorem cylinderCoordinate_nonneg (π : ℕ → ScanRule) (i : ℕ) (σ : List Bool) (a : ℕ) :
    0 ≤ cylinderCoordinate π i σ a :=
  integral_nonneg fun Z => (PoolQuery.indicator_bounds (π i) a Z).1

theorem cylinderCoordinate_le_one (π : ℕ → ScanRule) (i : ℕ) (σ : List Bool) (a : ℕ) :
    cylinderCoordinate π i σ a ≤ 1 := by
  calc
    cylinderCoordinate π i σ a ≤ ∫ _Z in cylinder σ, (1 : ℝ) ∂fairCoin :=
      integral_mono (PoolQuery.integrable_indicator (π i) a).restrict
        (integrable_const 1) fun Z => (PoolQuery.indicator_bounds (π i) a Z).2
    _ = fairCoin.real (cylinder σ) := by simp
    _ ≤ 1 := measureReal_le_one

theorem cylinderApprox_nonneg (π : ℕ → ScanRule) (i : ℕ) (σ : List Bool) (a V : ℕ) :
    0 ≤ cylinderApprox π i σ a V := by
  apply (Rat.cast_nonneg (K := ℝ)).mp
  rw [cylinderApprox_eq_integral]
  exact integral_nonneg fun Z => (PoolQuery.indicatorBy_bounds (π i) a V Z).1

theorem cylinderApprox_sound (π : ℕ → ScanRule) (i : ℕ) (σ : List Bool) (a V : ℕ) :
    (cylinderApprox π i σ a V : ℝ) ≤ cylinderCoordinate π i σ a := by
  rw [cylinderApprox_eq_integral, cylinderCoordinate]
  exact integral_mono (PoolQuery.integrable_indicatorBy (π i) a V).restrict
    (PoolQuery.integrable_indicator (π i) a).restrict
    (PoolQuery.indicatorBy_le_indicator (π i) a V)

theorem cylinderApprox_monotone (π : ℕ → ScanRule) (i : ℕ) (σ : List Bool) (a : ℕ) :
    Monotone (cylinderApprox π i σ a) := by
  intro V W hVW
  apply (Rat.cast_le (K := ℝ)).mp
  rw [cylinderApprox_eq_integral, cylinderApprox_eq_integral]
  apply integral_mono (PoolQuery.integrable_indicatorBy (π i) a V).restrict
    (PoolQuery.integrable_indicatorBy (π i) a W).restrict
  intro Z
  by_cases h : PoolQuery.ReadsBy (π i) a V Z
  · simp [PoolQuery.indicatorBy, h, PoolQuery.readsBy_mono (π i) a hVW h]
  · simpa [PoolQuery.indicatorBy, h] using (PoolQuery.indicatorBy_bounds (π i) a W Z).1

theorem cylinderApprox_tendsto (π : ℕ → ScanRule) (i : ℕ) (σ : List Bool) (a : ℕ) :
    Tendsto (fun V => (cylinderApprox π i σ a V : ℝ)) atTop
      (𝓝 (cylinderCoordinate π i σ a)) := by
  simp only [cylinderApprox_eq_integral, cylinderCoordinate]
  apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
  · intro V
    exact (PoolQuery.measurable_indicatorBy (π i) a V).aestronglyMeasurable
  · exact integrable_const 1
  · intro V
    filter_upwards [] with Z
    simpa only [Real.norm_eq_abs, abs_of_nonneg (PoolQuery.indicatorBy_bounds (π i) a V Z).1]
      using (PoolQuery.indicatorBy_bounds (π i) a V Z).2
  · filter_upwards [] with Z
    apply tendsto_const_nhds.congr'
    filter_upwards [PoolQuery.eventually_indicatorBy_eq (π i) a Z] with V hV
    exact hV.symm

theorem cylinderApprox_complete (π : ℕ → ScanRule) (i : ℕ) (σ : List Bool)
    (a : ℕ) (r : ℚ) (hr : (r : ℝ) < cylinderCoordinate π i σ a) :
    ∃ V, r < cylinderApprox π i σ a V := by
  obtain ⟨V, hV⟩ := ((cylinderApprox_tendsto π i σ a).eventually (lt_mem_nhds hr)).exists
  exact ⟨V, (Rat.cast_lt (K := ℝ)).mp hV⟩

@[simp] theorem cylinderCoordinate_nil (π : ℕ → ScanRule) (i a : ℕ) :
    cylinderCoordinate π i [] a = Pool.queryProbability (π i) a := by
  simp [cylinderCoordinate, Pool.queryProbability]

theorem computable_cylinderApprox (π : ℕ → ScanRule)
    (hπ : Computable (fun p : ℕ × List Bool => (π p.1).query p.2))
    {α : Type*} [Primcodable α] {i a V : α → ℕ} {σ : α → List Bool}
    (hi : Computable i) (ha : Computable a) (hV : Computable V) (hσ : Computable σ) :
    Computable (fun x => cylinderApprox π (i x) (σ x) (a x) (V x)) := by
  have hlen := Computable.list_length.comp hσ
  have hdepth := Primrec.nat_max.to_comp.comp hV hlen
  have hread := computable_reads π hπ (hi.comp Computable.fst) (ha.comp Computable.fst)
    (hV.comp Computable.fst) Computable.snd
  have hprefix := Primrec.eq.decide.to_comp.comp
    (Primrec.list_take.to_comp.comp (hlen.comp Computable.fst) Computable.snd)
    (hσ.comp Computable.fst)
  have hvalue := Computable.cond hprefix
    (Computable.cond hread (Computable.const (1 : ℚ)) (Computable.const 0))
    (Computable.const 0)
  exact (PoolAdvice.computable_average hdepth hvalue.to₂).of_eq fun _ => by
    simp only [cylinderApprox, Bool.cond_eq_ite, decide_eq_true_eq]

/-- Finite weighted lower approximation; both truncations use the same stage. -/
def weightedApprox (π : ℕ → ScanRule) (a V : ℕ) : ℚ :=
  PoolAdvice.boundedSum (fun i => PoolAdvice.weight i * cylinderApprox π i [] a V) V

theorem weightedApprox_eq_sum (π : ℕ → ScanRule) (a V : ℕ) :
    weightedApprox π a V =
      ∑ i ∈ Finset.range V, PoolAdvice.weight i * cylinderApprox π i [] a V := by
  have h (f : ℕ → ℚ) (n : ℕ) : PoolAdvice.boundedSum f n = ∑ i ∈ Finset.range n, f i := by
    induction n with
    | zero => simp [PoolAdvice.boundedSum]
    | succ n ih => simp [PoolAdvice.boundedSum, Finset.sum_range_succ, ih]
  exact h _ _

theorem weightedApprox_nonneg (π : ℕ → ScanRule) (a V : ℕ) :
    0 ≤ weightedApprox π a V := by
  rw [weightedApprox_eq_sum]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (by unfold PoolAdvice.weight; positivity)
    (cylinderApprox_nonneg π i [] a V)

theorem weightedApprox_monotone (π : ℕ → ScanRule) (a : ℕ) :
    Monotone (weightedApprox π a) := by
  intro V W hVW
  rw [weightedApprox_eq_sum, weightedApprox_eq_sum]
  calc
    _ ≤ ∑ i ∈ Finset.range V, PoolAdvice.weight i * cylinderApprox π i [] a W :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
        (cylinderApprox_monotone π i [] a hVW) (by unfold PoolAdvice.weight; positivity)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hVW)
      (fun i _ _ => mul_nonneg (by unfold PoolAdvice.weight; positivity)
        (cylinderApprox_nonneg π i [] a W))

theorem weightedApprox_sound (π : ℕ → ScanRule) (a V : ℕ) :
    (weightedApprox π a V : ℝ) ≤ Pool.weightedQueryProbability π a := by
  rw [weightedApprox_eq_sum]
  push_cast
  calc
    _ ≤ ∑ i ∈ Finset.range V, Pool.weight i * Pool.queryProbability (π i) a := by
      apply Finset.sum_le_sum
      intro i hi
      have h := cylinderApprox_sound π i [] a V
      simpa only [PoolAdvice.weight, Pool.weight, Rat.cast_pow, Rat.cast_div,
        Rat.cast_one, Rat.cast_ofNat, cylinderCoordinate_nil] using
        mul_le_mul_of_nonneg_left h (Pool.weight_nonneg i)
    _ ≤ _ := (Pool.summable_weighted_query π a).sum_le_tsum _
      (fun i _ => Pool.weighted_term_nonneg π a i)

theorem weightedApprox_tendsto (π : ℕ → ScanRule) (a : ℕ) :
    Tendsto (fun V => (weightedApprox π a V : ℝ)) atTop
      (𝓝 (Pool.weightedQueryProbability π a)) := by
  let f : ℕ → ℕ → ℝ := fun V i =>
    if i < V then Pool.weight i * (cylinderApprox π i [] a V : ℝ) else 0
  have hf (i : ℕ) : Tendsto (fun V => f V i) atTop
      (𝓝 (Pool.weight i * Pool.queryProbability (π i) a)) := by
    have hlim := (cylinderApprox_tendsto π i [] a).const_mul (Pool.weight i)
    rw [cylinderCoordinate_nil] at hlim
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop i] with V hV
    simp [f, hV]
  have hbound : ∀ V i, ‖f V i‖ ≤ Pool.weight i := by
    intro V i
    have h0 : 0 ≤ (cylinderApprox π i [] a V : ℝ) := by
      exact_mod_cast cylinderApprox_nonneg π i [] a V
    have h1 : (cylinderApprox π i [] a V : ℝ) ≤ 1 :=
      (cylinderApprox_sound π i [] a V).trans (cylinderCoordinate_le_one π i [] a)
    by_cases hi : i < V
    · simp only [f, hi, ite_true, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Pool.weight_nonneg i) h0)]
      exact mul_le_of_le_one_right (Pool.weight_nonneg i) h1
    · simpa [f, hi] using Pool.weight_nonneg i
  have h := tendsto_tsum_of_dominated_convergence Pool.summable_weight hf
    (Eventually.of_forall hbound)
  have he (V : ℕ) : (weightedApprox π a V : ℝ) = ∑' i, f V i := by
    rw [weightedApprox_eq_sum, tsum_eq_sum (s := Finset.range V)
      (fun i hi => by simp [f, show ¬ i < V from fun h => hi (Finset.mem_range.mpr h)])]
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    simp [f, Finset.mem_range.mp hi, PoolAdvice.weight, Pool.weight]
  simpa only [← he, Pool.weightedQueryProbability] using h

theorem weightedApprox_complete (π : ℕ → ScanRule) (a : ℕ) (r : ℚ)
    (hr : (r : ℝ) < Pool.weightedQueryProbability π a) :
    ∃ V, r < weightedApprox π a V := by
  obtain ⟨V, hV⟩ := ((weightedApprox_tendsto π a).eventually (lt_mem_nhds hr)).exists
  exact ⟨V, (Rat.cast_lt (K := ℝ)).mp hV⟩

theorem computable_weightedApprox (π : ℕ → ScanRule)
    (hπ : Computable (fun p : ℕ × List Bool => (π p.1).query p.2)) :
    Computable₂ (weightedApprox π) := by
  have hc := computable_cylinderApprox π hπ (α := (ℕ × ℕ) × ℕ)
    Computable.snd (Computable.fst.comp Computable.fst)
    (Computable.snd.comp Computable.fst) (Computable.const [])
  have hterm := primrec_rat_mul.to_comp.comp
    (PoolAdvice.computable_weight.comp Computable.snd) hc
  exact ((PoolAdvice.computable_boundedSum hterm.to₂).comp
    (Computable.id.pair Computable.snd)).of_eq fun _ => rfl

/-- Every simulator/cylinder pair has a numerical coordinate index. -/
def coordinateData (e : ℕ) : ℕ × List Bool := (Encodable.decode e).getD (0, [])

theorem primrec_coordinateData : Primrec coordinateData :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const (0, []))

@[simp] theorem coordinateData_encode (i : ℕ) (σ : List Bool) :
    coordinateData (Encodable.encode (i, σ)) = (i, σ) := by simp [coordinateData]

/-- Coordinate zero is the weighted probability; all later coordinates are
cylinder integrals of individual query indicators. -/
noncomputable def coordinate (π : ℕ → ScanRule) : ℕ → ℕ → ℝ
  | 0, a => Pool.weightedQueryProbability π a
  | e + 1, a => cylinderCoordinate π (coordinateData e).1 (coordinateData e).2 a

def approx (π : ℕ → ScanRule) : ℕ → ℕ → ℕ → ℚ
  | 0, a, V => weightedApprox π a V
  | e + 1, a, V => cylinderApprox π (coordinateData e).1 (coordinateData e).2 a V

@[simp] theorem coordinate_zero (π : ℕ → ScanRule) (a : ℕ) :
    coordinate π 0 a = Pool.weightedQueryProbability π a := rfl

@[simp] theorem coordinate_cylinder (π : ℕ → ScanRule) (i : ℕ) (σ : List Bool) (a : ℕ) :
    coordinate π (Encodable.encode (i, σ) + 1) a = cylinderCoordinate π i σ a := by
  simp only [coordinate, coordinateData_encode]

/-- These are also the cylinder coordinates of the existing Hilbert-space
query vectors, so scalar extraction connects directly to their weak limits. -/
theorem coordinate_cylinder_queryL2 (π : ℕ → ScanRule) (i : ℕ) (σ : List Bool) (a : ℕ) :
    coordinate π (Encodable.encode (i, σ) + 1) a =
      ∫ Z in cylinder σ, Pool.queryL2 (π i) a Z ∂fairCoin := by
  rw [coordinate_cylinder, cylinderCoordinate]
  exact integral_congr_ae (ae_restrict_of_ae (Pool.queryL2_coeFn (π i) a).symm)

theorem coordinate_nonneg (π : ℕ → ScanRule) (e a : ℕ) : 0 ≤ coordinate π e a := by
  cases e with
  | zero => exact Pool.weightedQueryProbability_nonneg π a
  | succ e => exact cylinderCoordinate_nonneg π _ _ a

theorem coordinate_le_one (π : ℕ → ScanRule) (e a : ℕ) : coordinate π e a ≤ 1 := by
  cases e with
  | zero => exact Pool.weightedQueryProbability_le_one π a
  | succ e => exact cylinderCoordinate_le_one π _ _ a

theorem computable_approx (π : ℕ → ScanRule)
    (hπ : Computable (fun p : ℕ × List Bool => (π p.1).query p.2)) :
    Computable (fun z : ℕ × ℕ × ℕ => approx π z.1 z.2.1 z.2.2) := by
  have hzero : Computable (fun z : ℕ × ℕ × ℕ => weightedApprox π z.2.1 z.2.2) :=
    (computable_weightedApprox π hπ).comp
    (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd)
  have hd := primrec_coordinateData.to_comp.comp
    (Computable.snd : Computable (fun p : (ℕ × ℕ × ℕ) × ℕ => p.2))
  have hsucc := computable_cylinderApprox π hπ (Computable.fst.comp hd)
    (Computable.fst.comp (Computable.snd.comp Computable.fst))
    (Computable.snd.comp (Computable.snd.comp Computable.fst)) (Computable.snd.comp hd)
  exact (Computable.nat_casesOn Computable.fst hzero hsucc.to₂).of_eq
    fun z => by cases z.1 <;> rfl

/-- A uniformly computable scan family gives genuine ordinary left-c.e.
names for all its query coordinates. -/
def lowerName (π : ℕ → ScanRule)
    (hπ : Computable (fun p : ℕ × List Bool => (π p.1).query p.2)) :
    LeftCeReservoir.LowerName (coordinate π) where
  approx := approx π
  computable := computable_approx π hπ
  monotone := by
    intro e a
    cases e with
    | zero => exact weightedApprox_monotone π a
    | succ e => exact cylinderApprox_monotone π _ _ a
  sound := by
    intro e a V
    cases e with
    | zero => exact weightedApprox_sound π a V
    | succ e => exact cylinderApprox_sound π _ _ a V
  complete := by
    intro e a r hr
    cases e with
    | zero => exact weightedApprox_complete π a r hr
    | succ e => exact cylinderApprox_complete π _ _ a r hr

/-- The actual scans from the success-covering total simulator family. -/
def simulatorScan (i : ℕ) : ScanRule := (UniformStrategyFamily.strategy i).scan

/-- The concrete lower name used by effective coordinate extraction. -/
def simulatorLowerName : LeftCeReservoir.LowerName (coordinate simulatorScan) :=
  lowerName simulatorScan UniformStrategyFamily.primrec_query.to_comp

end Klr.EffectiveQueryCoordinates
