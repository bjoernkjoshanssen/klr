module

public import Klr.PoolConstruction

/-!
# Pool parameters with a local weighted-mass bound

The scalar limit need not be the global weighted limsup. The finite advice
can be chosen around any weighted limit of the fixed query subsequence.
Soundness only requires an upper weighted-mass bound on positions actually
returned by the pool program. This permits search inside a computably
enumerable reservoir and avoids an effective global maximization step.
-/

@[expose] public section

namespace Klr.PoolReservoir

open Filter MeasureTheory PoolAdvice
open scoped BigOperators Topology symmDiff

/-- All finite data and their analytic guarantees, chosen before the pool size. -/
structure Parameters {π : ℕ → ScanRule} {a : ℕ → ℕ}
    (Q : Pool.QueryPartition π a) (ℓ : ℕ) (η : ℝ) (z : ℕ) (pstar : ℝ) where
  margin : ℚ
  scanCount : ℕ
  advice : Advice
  margin_pos : 0 < margin
  margin_lt_quarter : margin < 1 / 4
  protected_eq : advice.protectedCount = ℓ
  protected_le : ℓ ≤ scanCount
  position_ge : z ≤ advice.positionBound
  error_pos : 0 < advice.error
  high_budget : 4 * (advice.error : ℝ) < η
  low_budget : η / 3 + 8 * (advice.error : ℝ) / (margin : ℝ) < η
  near_one : ∀ i < ℓ, fairCoin.real
    {Z | Z ∈ Q.low i ∧ 1 - 2 * (margin : ℝ) ≤ Q.representative i Z} < η / 3
  high_approx : ∀ i < ℓ,
    fairCoin.real (Q.high i ∆ highSet advice i) < (advice.error : ℝ)
  function_approx : ∀ i < ℓ,
    (∫ Z, |approx advice i Z - Q.representative i Z| ∂fairCoin) < (advice.error : ℝ)
  approx_bounds : ∀ i < ℓ, ∀ Z, 0 ≤ approx advice i Z ∧ approx advice i Z ≤ 1
  threshold_lower : pstar -
    3 * (protectedWeight advice * (advice.error : ℝ)) < (advice.threshold : ℝ)
  threshold_upper : (advice.threshold : ℝ) < pstar -
    2 * (protectedWeight advice * (advice.error : ℝ))
  tail_lt : (1 / 2 : ℝ) ^ scanCount <
    (protectedWeight advice * (advice.error : ℝ)) / 4

/-- All scalar parameters and all finite prefix tables can be chosen jointly,
with the complete finite advice fixed before a later input M. -/
theorem exists_parameters {π : ℕ → ScanRule} {a : ℕ → ℕ}
    (Q : Pool.QueryPartition π a) (ℓ : ℕ) {η : ℝ} (hη : 0 < η) (z : ℕ) (pstar : ℝ) :
    Nonempty (Parameters Q ℓ η z pstar) := by
  obtain ⟨τ, hτ0, hτ1, hmargin⟩ := Q.exists_rational_margin ℓ (show 0 < η / 3 by positivity)
  have hτr : (0 : ℝ) < τ := by exact_mod_cast hτ0
  obtain ⟨δ, hδ0, hδsmall⟩ := exists_rat_btwn
    (show (0 : ℝ) < min (η / 4) (η * (τ : ℝ) / 24) by positivity)
  have hδq : (0 : ℚ) < δ := by exact_mod_cast hδ0
  have hδsmall₁ : (δ : ℝ) < η / 4 := hδsmall.trans_le (min_le_left _ _)
  have hδsmall₂ : (δ : ℝ) < η * (τ : ℝ) / 24 := hδsmall.trans_le (min_le_right _ _)
  have hhigh : 4 * (δ : ℝ) < η := by linarith
  have hlow : η / 3 + 8 * (δ : ℝ) / (τ : ℝ) < η := by
    have hdiv : 8 * (δ : ℝ) / (τ : ℝ) < η / 3 := by
      apply (div_lt_iff₀ hτr).mpr
      nlinarith
    linarith
  let s : ℝ := (1 / 2 : ℝ) ^ ℓ * (δ : ℝ)
  have hs : 0 < s := mul_pos (pow_pos (by norm_num) _) hδ0
  obtain ⟨γ, hγlow, hγhigh⟩ := exists_rat_btwn
    (show pstar - 3 * s < pstar - 2 * s by linarith)
  have htail : ∀ᶠ k : ℕ in atTop, (1 / 2 : ℝ) ^ k < s / 4 :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).eventually (gt_mem_nhds (by positivity))
  obtain ⟨D, hD, hDtail⟩ := ((eventually_ge_atTop ℓ).and htail).exists
  obtain ⟨A, hAz, hAℓ, hAδ, hAγ, hAtables⟩ := exists_approximating_advice ℓ
    z ℓ δ γ hδq (fun i => Q.high i.val) (fun i => Q.measurableSet_high i.val)
    (fun i => Q.representative i.val) (fun i => Q.measurable_representative i.val)
    (fun i Z => (Q.representative_bounds i.val Z).1)
    (fun i Z => (Q.representative_bounds i.val Z).2)
  have hsA : protectedWeight A * (A.error : ℝ) = s := by
    simp only [protectedWeight, hAℓ, hAδ, s]
  refine ⟨{
    margin := τ
    scanCount := D
    advice := A
    margin_pos := hτ0
    margin_lt_quarter := hτ1
    protected_eq := hAℓ
    protected_le := hD
    position_ge := ?_
    error_pos := ?_
    high_budget := ?_
    low_budget := ?_
    near_one := hmargin
    high_approx := ?_
    function_approx := ?_
    approx_bounds := ?_
    threshold_lower := ?_
    threshold_upper := ?_
    tail_lt := ?_ }⟩
  · exact hAz.ge
  · rwa [hAδ]
  · rwa [hAδ]
  · rwa [hAδ]
  · intro i hi
    rw [hAδ, symmDiff_comm]
    exact (hAtables ⟨i, hi⟩).1
  · intro i hi
    rw [hAδ]
    exact (hAtables ⟨i, hi⟩).2.2
  · intro i hi Z
    exact (hAtables ⟨i, hi⟩).2.1 Z
  · rwa [hsA, hAγ]
  · rwa [hsA, hAγ]
  · rwa [hsA]

namespace Parameters

variable {π : ℕ → ScanRule} {a : ℕ → ℕ} {Q : Pool.QueryPartition π a}
  {ℓ : ℕ} {η : ℝ} {z : ℕ} {pstar : ℝ} (P : Parameters Q ℓ η z pstar)

/-- The fixed finite family of actual total computable scans compiled by the search. -/
def rules : List ScanRule := List.ofFn (fun i : Fin P.scanCount => π i.val)

@[simp] theorem length_rules : P.rules.length = P.scanCount := List.length_ofFn

theorem getElem?_rules {i : ℕ} (hi : i < P.scanCount) : P.rules[i]? = some (π i) := by
  simp [rules, hi]

theorem protected_le_length : P.advice.protectedCount ≤ P.rules.length := by
  rw [P.protected_eq, P.length_rules]
  exact P.protected_le

theorem error_real_pos : (0 : ℝ) < P.advice.error := by exact_mod_cast P.error_pos

theorem margin_real_pos : (0 : ℝ) < P.margin := by exact_mod_cast P.margin_pos

theorem slack_pos : 0 < protectedWeight P.advice * (P.advice.error : ℝ) :=
  mul_pos (protectedWeight_pos P.advice) P.error_real_pos

/-- The chosen threshold leaves less than the permitted later-increase budget. -/
theorem weighted_gap : pstar +
    protectedWeight P.advice * (P.advice.error : ℝ) - (P.advice.threshold : ℝ) <
      4 * protectedWeight P.advice * (P.advice.error : ℝ) := by
  have h := P.threshold_lower
  nlinarith

/-- The geometric tail is small enough for the finite weighted limit to be
strictly above the acceptance threshold. -/
theorem threshold_add_tail_lt :
    (P.advice.threshold : ℝ) + (1 / 2 : ℝ) ^ P.scanCount < pstar := by
  have h₁ := P.threshold_upper
  have h₂ := P.tail_lt
  have h₃ := P.slack_pos
  linarith

/-- The rational and real weight conventions coincide. -/
theorem cast_weight_eq (i : ℕ) : (PoolAdvice.weight i : ℝ) = Pool.weight i := by
  simp [PoolAdvice.weight, Pool.weight]

/-- The strict near-one strip used in the L1 argument is bounded by the
fixed low-set strip used to choose the margin. -/
theorem near_one_strict {i : ℕ} (hi : i < ℓ) :
    fairCoin.real {Z | 1 - 2 * (P.margin : ℝ) < Q.representative i Z ∧
      Q.representative i Z < 1} < η / 3 := by
  apply lt_of_le_of_lt (measureReal_mono (μ := fairCoin) ?_) (P.near_one i hi)
  intro Z hZ
  refine ⟨?_, hZ.1.le⟩
  change Q.representative i Z ≠ 1
  exact ne_of_lt hZ.2

/-- Fixed representatives are integrable on the probability space. -/
theorem integrable_representative (i : ℕ) : Integrable (Q.representative i) fairCoin :=
  (Pool.integrable_L2 (Q.limit i)).congr (Q.representative_ae_eq i).symm

/-- A weighted upper bound is needed only at the selected pool positions. -/
theorem final_weighted_bound (hpstar : 0 ≤ pstar) (G : Finset ℕ)
    (hG : ∀ b ∈ G, Pool.weightedQueryProbability π b ≤
      pstar + protectedWeight P.advice * (P.advice.error : ℝ)) :
    (∑ i ∈ Finset.range P.scanCount,
      (PoolAdvice.weight i : ℝ) * ∫ Z, PoolQuery.readFraction (π i) G Z ∂fairCoin) ≤
      pstar + protectedWeight P.advice * (P.advice.error : ℝ) := by
  have hInt (i : ℕ) : (∫ Z, PoolQuery.readFraction (π i) G Z ∂fairCoin) =
      (∑ b ∈ G, Pool.queryProbability (π i) b) / G.card := by
    unfold PoolQuery.readFraction Pool.queryProbability
    rw [integral_div,
      integral_finsetSum _ (fun b _ => PoolQuery.integrable_indicator (π i) b)]
  simp_rw [hInt, cast_weight_eq, ← mul_div_assoc, Finset.mul_sum]
  rw [← Finset.sum_div, Finset.sum_comm]
  by_cases hcard : G.card = 0
  · simp only [hcard, Nat.cast_zero, div_zero]
    exact add_nonneg hpstar P.slack_pos.le
  · apply (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hcard)).mpr
    calc
      _ ≤ ∑ _b ∈ G, (pstar +
          protectedWeight P.advice * (P.advice.error : ℝ)) := by
        apply Finset.sum_le_sum
        intro b hb
        exact (sub_nonneg.mp (Pool.weighted_query_truncation π b P.scanCount).1).trans
          (hG b hb)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- Every accepted pair satisfies both final measure estimates on the fixed
Borel partition. The finite tables are used only inside the computation. -/
theorem accepted_measure_bounds {M : ℕ} {C : Candidate}
    (h : Accepted P.rules P.advice M C) (hpstar : 0 ≤ pstar)
    (hupper : ∀ b ∈ C.1, Pool.weightedQueryProbability π b ≤
      pstar + protectedWeight P.advice * (P.advice.error : ℝ)) :
    ∀ i < ℓ,
      fairCoin.real {Z | Z ∈ Q.high i ∧ PoolQuery.readFraction (π i) C.1.toFinset Z < 1} < η ∧
      fairCoin.real {Z | Z ∈ Q.low i ∧
        1 - (P.margin : ℝ) < PoolQuery.readFraction (π i) C.1.toFinset Z} < η := by
  have hπ : ∀ i < P.rules.length, P.rules[i]? = some (π i) := by
    intro i hi
    exact P.getElem?_rules (by simpa only [P.length_rules] using hi)
  have hbound : (∑ i ∈ Finset.range P.rules.length,
      (PoolAdvice.weight i : ℝ) *
        ∫ Z, PoolQuery.readFraction (π i) C.1.toFinset Z ∂fairCoin) ≤
      pstar + protectedWeight P.advice * (P.advice.error : ℝ) := by
    rw [P.length_rules]
    exact P.final_weighted_bound hpstar _ (fun b hb => hupper b (List.mem_toFinset.mp hb))
  intro i hi
  have hi' : i < P.advice.protectedCount := by rwa [P.protected_eq]
  refine ⟨?_, ?_⟩
  · exact (h.high_failure_lt π hπ P.protected_le_length hi' (P.high_approx i hi)).trans
      P.high_budget
  · have hlow := h.low_near_full_lt π hπ P.protected_le_length hbound P.weighted_gap hi'
      (integrable_representative (Q := Q) i) (P.function_approx i hi) P.margin_real_pos
      (P.near_one_strict hi)
    apply lt_of_le_of_lt (measureReal_mono (μ := fairCoin) ?_) (hlow.trans P.low_budget)
    intro Z hZ
    exact ⟨Q.representative_lt_one_on_low i hZ.1, hZ.2⟩

/-- Any scalar weighted limit supplies the required eventual lower bound. -/
theorem eventually_weighted_above
    (hp : Tendsto (Pool.weightedQueryProbability π ∘ Q.position) atTop
      (𝓝 (pstar))) :
    ∀ᶠ n : ℕ in atTop, (P.advice.threshold : ℝ) <
      ∑ i ∈ Finset.range P.rules.length,
        Pool.weight i * Pool.queryProbability (π i) (Q.position n) := by
  obtain ⟨ε, hε, hev⟩ := Q.eventually_finite_weighted_above hp P.scanCount
    P.threshold_add_tail_lt
  filter_upwards [hev] with n hn
  rw [P.length_rules]
  linarith

/-- Local weighted control and finite acceptance imply the original pool contract. -/
theorem goodPool_of_accepted {M : ℕ} {C : Candidate}
    (h : Accepted P.rules P.advice M C) (hpstar : 0 ≤ pstar)
    (hupper : ∀ b ∈ C.1, Pool.weightedQueryProbability π b ≤
      pstar + protectedWeight P.advice * (P.advice.error : ℝ)) :
    PoolConstruction.GoodPool π Q.high ℓ η z P.margin M C.1 := by
  refine ⟨h.1, h.2.1, fun b hb => P.position_ge.trans (h.2.2.1 b hb), ?_⟩
  intro i hi
  have hbounds := P.accepted_measure_bounds h hpstar hupper i hi
  refine ⟨?_, ?_⟩
  · apply lt_of_le_of_lt (measureReal_mono (μ := fairCoin) ?_) hbounds.1
    intro Z hZ
    refine ⟨hZ.1, PoolQuery.readFraction_lt_one_of_exists_missed (π i) Z ?_⟩
    obtain ⟨b, hb, hmiss⟩ := hZ.2
    exact ⟨b, List.mem_toFinset.mpr hb, hmiss⟩
  · apply lt_of_le_of_lt (measureReal_mono (μ := fairCoin) ?_) hbounds.2
    intro Z hZ
    refine ⟨hZ.1, PoolQuery.one_sub_lt_readFraction_of_missedCount_lt
      (π i) C.1.toFinset Z (P.margin : ℝ) ?_⟩
    rw [List.toFinset_card_of_nodup h.2.1, h.1]
    exact hZ.2

end Parameters

end Klr.PoolReservoir
