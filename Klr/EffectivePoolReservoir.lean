module

public import Klr.PoolReservoirParameters
public import Klr.EffectiveSearch

/-!
# Ordinary pool search inside computably enumerable reservoirs

A fixed query weak limit need not maximize the global weighted query mass.
For each desired error it suffices to have a computably enumerable reservoir
containing eventually all positions of the subsequence, with weighted mass
uniformly below the limiting mass plus that error on the reservoir.

The program still has no oracle. A nonempty c.e. reservoir has a primitive
recursive enumeration with repetitions, so exhaustive finite pool search can
be restricted to that enumeration before the requested pool size is known.
-/

@[expose] public section

namespace Klr.PoolReservoir

open Filter MeasureTheory PoolAdvice
open scoped Topology BigOperators symmDiff

/-- A nonempty c.e. set has a primitive recursive enumeration with repetitions.
The bounded recognizer returns a fixed member on unsuccessful trials. -/
theorem exists_primrec_range {S : Set ℕ} (hS : REPred (fun n => n ∈ S))
    (hne : S.Nonempty) : ∃ f : ℕ → ℕ, Primrec f ∧ Set.range f = S := by
  obtain ⟨c, hc⟩ := exists_programAccepts hS
  obtain ⟨b₀, hb₀⟩ := hne
  let f : ℕ → ℕ := fun z =>
    if (Nat.Partrec.Code.evaln (Nat.unpair z).2 c (Nat.unpair z).1).isSome then
      (Nat.unpair z).1 else b₀
  let fst := Primrec.fst.comp Primrec.unpair
  let snd := Primrec.snd.comp Primrec.unpair
  have ht := Nat.Partrec.Code.primrec_evaln.comp ((snd.pair (Primrec.const c)).pair fst)
  have hf : Primrec f := (Primrec.cond (Primrec.option_isSome.comp ht) fst
    (Primrec.const b₀)).of_eq (fun z => by simp [f, Bool.cond_eq_ite])
  refine ⟨f, hf, Set.ext fun b => ?_⟩
  constructor
  · rintro ⟨z, rfl⟩
    dsimp [f]
    split_ifs with h
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
      apply (hc _).mp
      exact Part.dom_iff_mem.mpr ⟨v, Nat.Partrec.Code.evaln_sound hv⟩
    · exact hb₀
  · intro hb
    obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp ((hc b).mpr hb)
    obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp hv
    have ht' : v ∈ Nat.Partrec.Code.evaln t c b := by simpa using ht
    have hs : (Nat.Partrec.Code.evaln t c b).isSome = true := Option.isSome_of_mem ht'
    exact ⟨Nat.pair b t, by simp only [f, Nat.unpair_pair, hs, ↓reduceIte]⟩

/-- Map finite candidate indices into the chosen reservoir. -/
def mapCandidate (f : ℕ → ℕ) (C : Candidate) : Candidate := (C.1.map f, C.2)

theorem primrec_mapCandidate {f : ℕ → ℕ} (hf : Primrec f) :
    Primrec (mapCandidate f) :=
  (Primrec.list_map Primrec.fst (hf.comp Primrec.snd).to₂).pair Primrec.snd

/-- A bounded trial searches the original finite tests on mapped candidates. -/
def trial (rules : List ScanRule) (A : Advice) (f : ℕ → ℕ)
    (M n : ℕ) : Option Candidate :=
  (@Encodable.decode Candidate (inferInstance : Primcodable Candidate).toEncodable n).bind
    fun C => if check rules A M (mapCandidate f C) then some (mapCandidate f C) else none

theorem computable_trial (rules : List ScanRule) (A : Advice) {f : ℕ → ℕ}
    (hf : Primrec f) : Computable₂ (trial rules A f) := by
  have hmap := (primrec_mapCandidate hf).to_comp
  have hcheck := (computable_check rules A).comp
    Computable.fst (hmap.comp Computable.snd)
  have h : Computable₂ (fun M C => if check rules A M (mapCandidate f C) then
      some (mapCandidate f C) else none) := by
    exact (Computable.cond hcheck (Computable.option_some.comp
      (hmap.comp Computable.snd)) (Computable.const none)).of_eq
        (fun _ => by simp [Bool.cond_eq_ite])
  exact Computable.bind_decode_iff.mpr h

/-- The fixed partial-recursive search restricted to the reservoir range. -/
def search (rules : List ScanRule) (A : Advice) (f : ℕ → ℕ) (M : ℕ) : Part Candidate :=
  Nat.rfindOpt (trial rules A f M)

theorem partrec_search (rules : List ScanRule) (A : Advice) {f : ℕ → ℕ}
    (hf : Primrec f) : Partrec (search rules A f) :=
  Partrec.rfindOpt (computable_trial rules A hf)

theorem search_spec {rules : List ScanRule} {A : Advice} {f : ℕ → ℕ}
    {M : ℕ} {C : Candidate} (hC : C ∈ search rules A f M) :
    Accepted rules A M C ∧ ∀ b ∈ C.1, b ∈ Set.range f := by
  obtain ⟨n, hn⟩ := Nat.rfindOpt_spec hC
  simp only [trial, Option.mem_bind_iff] at hn
  obtain ⟨B, _, hB⟩ := hn
  split_ifs at hB with hv
  · have he : mapCandidate f B = C := Option.mem_some_iff.mp hB
    subst C
    refine ⟨(check_eq_true rules A M _).mp hv, ?_⟩
    intro b hb
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hb
    exact ⟨a, rfl⟩
  · simp at hB

/-- Every accepted candidate whose positions lie in the range is eventually
found; no decision procedure for the reservoir is required. -/
theorem search_dom {rules : List ScanRule} {A : Advice} {f : ℕ → ℕ}
    {M : ℕ} {C : Candidate} (hC : Accepted rules A M C)
    (hrange : ∀ b ∈ C.1, b ∈ Set.range f) : (search rules A f M).Dom := by
  classical
  have hex (B : List ℕ) : (∀ b ∈ B, b ∈ Set.range f) →
      ∃ G : List ℕ, G.map f = B := by
    induction B with
    | nil => exact fun _ => ⟨[], rfl⟩
    | cons b bs ih =>
      intro hB
      obtain ⟨a, ha⟩ := hB b (by simp)
      obtain ⟨G, hG⟩ := ih (fun x hx => hB x (by simp [hx]))
      exact ⟨a :: G, by simp [ha, hG]⟩
  obtain ⟨G, hG⟩ := hex C.1 hrange
  apply Nat.rfindOpt_dom.mpr
  refine ⟨encodeCandidate (G, C.2), C, ?_⟩
  have he : mapCandidate f (G, C.2) = C := by
    ext <;> simp [mapCandidate, hG]
  simp only [trial, encodeCandidate, Encodable.encodek, Option.bind_some, he]
  rw [(check_eq_true rules A M C).mpr hC]
  exact Option.mem_some_self C

/-- One ordinary program returns accepted reservoir pools at all large sizes. -/
theorem exists_eventual_program (rules : List ScanRule) (A : Advice) {f : ℕ → ℕ}
    (hf : Primrec f)
    (h : ∀ᶠ M in atTop, ∃ C, Accepted rules A M C ∧ ∀ b ∈ C.1, b ∈ Set.range f) :
    ∃ e : Nat.Partrec.Code, ∀ᶠ M in atTop,
      ∃ G V, encodePool G ∈ e.eval M ∧ Accepted rules A M (G, V) ∧
        ∀ b ∈ G, b ∈ Set.range f := by
  let pool : ℕ → Part (List ℕ) := fun M => (search rules A f M).map Prod.fst
  have hp : Partrec pool := (partrec_search rules A hf).map
    (Computable.fst.comp Computable.snd)
  obtain ⟨e, he⟩ := Nat.Partrec.Code.exists_code.mp hp
  have he' (M : ℕ) : e.eval M = (pool M).map encodePool := by
    rw [he]
    simp only [Encodable.decode_nat, Part.coe_some, Part.bind_some]
    rfl
  refine ⟨e, ?_⟩
  filter_upwards [h] with M hM
  obtain ⟨C, hC, hrange⟩ := hM
  obtain ⟨B, hB⟩ := Part.dom_iff_mem.mp (search_dom hC hrange)
  have hs := search_spec hB
  refine ⟨B.1, B.2, ?_, hs.1, hs.2⟩
  rw [he']
  exact Part.mem_map encodePool (Part.mem_map Prod.fst hB)

end Klr.PoolReservoir

namespace Klr.Pool.QueryPartition

open Filter MeasureTheory
open scoped Topology BigOperators symmDiff

/-- The weak-sample selection preserves membership in any eventual reservoir. -/
theorem eventually_exists_final_pool_in {π : ℕ → ScanRule} {a : ℕ → ℕ}
    (D : QueryPartition π a) (ha : Tendsto D.position atTop atTop)
    (ℓ k z : ℕ) {δ γ : ℝ} (hδ : 0 < δ)
    (hweighted : ∀ᶠ n : ℕ in atTop,
      γ < ∑ i ∈ Finset.range k, weight i * queryProbability (π i) (D.position n))
    (S : Set ℕ) (hS : ∀ᶠ n in atTop, D.position n ∈ S) :
    ∀ᶠ M : ℕ in atTop, ∃ G : Finset ℕ,
      G.card = M ∧ (∀ b ∈ G, b ∈ S) ∧ (∀ b ∈ G, z ≤ b) ∧
      (∀ i < ℓ, fairCoin.real {Z | Z ∈ D.high i ∧ PoolQuery.readFraction (π i) G Z < 1} < δ) ∧
      (∀ i < ℓ, (∫ Z, |PoolQuery.readFraction (π i) G Z - D.representative i Z| ∂fairCoin) < δ) ∧
      γ < finitePoolMass π k G := by
  classical
  have hselect := eventually_exists_finite_weak_average
    (fun i n => queryL2 (π i) (D.position n)) D.limit D.weak
    (fun i n => norm_queryL2_le_one (π i) (D.position n))
    (fun i => norm_le_one_of_ae_unitInterval (D.limit_nonneg i) (D.limit_le_one i))
    D.position ha ℓ hδ
  filter_upwards [eventually_ge_atTop 1, hselect] with M hM hselect
  have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  let P : ℕ → Prop := fun n => z ≤ D.position n ∧
    (∀ i < ℓ, fairCoin.real (D.high i \ {Z | PoolQuery.Reads (π i) (D.position n) Z}) <
      δ / M) ∧ γ < ∑ i ∈ Finset.range k, weight i * queryProbability (π i) (D.position n)
  have hP : ∀ᶠ n : ℕ in atTop, P n := by
    have hhigh : ∀ᶠ n : ℕ in atTop, ∀ i : Fin ℓ,
        fairCoin.real (D.high i \ {Z | PoolQuery.Reads (π i) (D.position n) Z}) < δ / M :=
      Filter.eventually_all.mpr fun i => (D.high_miss_tendsto_zero i).eventually
        (gt_mem_nhds (div_pos hδ hMr))
    filter_upwards [ha.eventually (eventually_ge_atTop z), hhigh, hweighted] with n hz hh hw
    exact ⟨hz, fun i hi => hh ⟨i, hi⟩, hw⟩
  obtain ⟨F, hcard, hPF', hinj, hnorm⟩ :=
    hselect (fun n => P n ∧ D.position n ∈ S) (hP.and hS)
  have hPF (n : ℕ) (hn : n ∈ F) : P n := (hPF' n hn).1
  let G := F.image D.position
  have hGcard : G.card = M := (Finset.card_image_of_injOn hinj).trans hcard
  have hG : G.Nonempty := Finset.card_pos.mp (by omega)
  have hF : F.Nonempty := Finset.card_pos.mp (by omega)
  have hside : ∀ b ∈ G, z ≤ b ∧
      (∀ i < ℓ, fairCoin.real (D.high i \ {Z | PoolQuery.Reads (π i) b Z}) < δ / M) ∧
      γ < ∑ i ∈ Finset.range k, weight i * queryProbability (π i) b := by
    intro b hb
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hb
    exact hPF n hn
  refine ⟨G, hGcard, ?_, fun b hb => (hside b hb).1, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hb
    exact (hPF' n hn).2
  · intro i hi
    calc
      _ ≤ ∑ b ∈ G, fairCoin.real (D.high i \ {Z | PoolQuery.Reads (π i) b Z}) :=
        PoolQuery.high_miss_le_sum (π i) hG (D.high i)
      _ < ∑ _b ∈ G, δ / (M : ℝ) :=
        Finset.sum_lt_sum_of_nonempty hG (fun b hb => (hside b hb).2.1 i hi)
      _ = δ := by simp [hGcard, nsmul_eq_mul, mul_div_cancel₀ δ hMr.ne']
  · intro i hi
    apply (D.integral_abs_readFraction_sub_representative_le i G).trans_lt
    rw [show G = F.image D.position from rfl, averageL2_image_sub _ _ _ hinj hF]
    exact hnorm i hi
  · rw [finitePoolMass_eq_average]
    apply (lt_div_iff₀ (by exact_mod_cast hG.card_pos)).mpr
    calc
      γ * (G.card : ℝ) = ∑ _b ∈ G, γ := by simp [mul_comm]
      _ < _ := Finset.sum_lt_sum_of_nonempty hG (fun b hb => (hside b hb).2.2)


end Klr.Pool.QueryPartition

namespace Klr.PoolReservoir

open Filter MeasureTheory PoolAdvice
open scoped Topology BigOperators symmDiff

/-- Finite-horizon acceptance retains the chosen pool itself. -/
theorem exists_accepted_on_pool {π : ℕ → ScanRule} {rules : List ScanRule}
    (hπ : ∀ i < rules.length, rules[i]? = some (π i)) (A : Advice)
    (hℓ : A.protectedCount ≤ rules.length) (hε : 0 < (A.error : ℝ))
    {M : ℕ} {G : Finset ℕ} (hcard : G.card = M)
    (hposition : ∀ b ∈ G, A.positionBound ≤ b)
    (hhigh : ∀ i < A.protectedCount,
      fairCoin.real {Z | Z ∈ highSet A i ∧ PoolQuery.readFraction (π i) G Z < 1} <
        2 * (A.error : ℝ))
    (hdist : ∀ i < A.protectedCount,
      (∫ Z, |PoolQuery.readFraction (π i) G Z - approx A i Z| ∂fairCoin) <
        2 * (A.error : ℝ))
    (hweighted : (A.threshold : ℝ) < Pool.finitePoolMass π rules.length G) :
    ∃ V, Accepted rules A M (G.toList, V) := by
  classical
  have hevHigh : ∀ᶠ V : ℕ in atTop, ∀ i : Fin A.protectedCount,
      fairCoin.real {Z | Z ∈ highSet A i ∧ PoolQuery.readFractionBy (π i) G V Z < 1} <
        3 * (A.error : ℝ) := by
    apply Filter.eventually_all.mpr
    intro i
    exact (PoolQuery.tendsto_high_missBy (π i) G (measurableSet_highSet A i)).eventually
      (p := fun x => x < 3 * (A.error : ℝ)) (gt_mem_nhds (by linarith [hhigh i i.isLt]))
  have hevDist : ∀ᶠ V : ℕ in atTop, ∀ i : Fin A.protectedCount,
      (∫ Z, |PoolQuery.readFraction (π i) G Z -
        PoolQuery.readFractionBy (π i) G V Z| ∂fairCoin) < (A.error : ℝ) := by
    exact Filter.eventually_all.mpr fun i =>
      (PoolQuery.tendsto_readFractionBy_l1 (π i) G).eventually (gt_mem_nhds hε)
  have hwlim : Tendsto (fun V : ℕ => (weightedMass rules A G.toList V : ℝ)) atTop
      (𝓝 (Pool.finitePoolMass π rules.length G)) := by
    simpa only [Finset.toList_toFinset] using
      tendsto_weightedMass hπ A G.toList G.nodup_toList
  have hevWeight := hwlim.eventually (lt_mem_nhds hweighted)
  obtain ⟨V, hVhigh, hVdist, hVweighted⟩ := (hevHigh.and (hevDist.and hevWeight)).exists
  refine ⟨V, ?_⟩
  refine ⟨?_, G.nodup_toList, ?_, ?_, ?_, ?_⟩
  · simpa only [Finset.length_toList] using hcard
  · intro b hb
    exact hposition b (Finset.mem_toList.mp hb)
  · intro i hi
    have hreal : (highMiss rules A G.toList V i : ℝ) < 3 * (A.error : ℝ) := by
      rw [highMiss_eq_measureReal (hπ i (hi.trans_le hℓ)) A G.toList G.nodup_toList V,
        Finset.toList_toFinset]
      exact hVhigh ⟨i, hi⟩
    exact_mod_cast hreal
  · intro i hi
    have hsmall : (∫ Z, |PoolQuery.readFractionBy (π i) G V Z -
        PoolQuery.readFraction (π i) G Z| ∂fairCoin) < (A.error : ℝ) := by
      simpa only [abs_sub_comm] using hVdist ⟨i, hi⟩
    have htri := PoolSoundness.integral_abs_sub_le_add
      (PoolQuery.integrable_readFractionBy (π i) G V)
      (PoolQuery.integrable_readFraction (π i) G) (integrable_approx A i)
    have hfinal := hdist i hi
    have hreal : (distance rules A G.toList V i : ℝ) < 3 * (A.error : ℝ) := by
      rw [distance_eq_integral (hπ i (hi.trans_le hℓ)) A G.toList G.nodup_toList V,
        Finset.toList_toFinset]
      linarith
    exact_mod_cast hreal
  · exact_mod_cast hVweighted


namespace Parameters

variable {π : ℕ → ScanRule} {a : ℕ → ℕ} {Q : Pool.QueryPartition π a}
  {ℓ : ℕ} {η : ℝ} {z : ℕ} {pstar : ℝ} (P : Parameters Q ℓ η z pstar)

/-- Analytic finite selection and horizon convergence retain the reservoir. -/
theorem eventually_accepted_in
    (ha : Tendsto Q.position atTop atTop)
    (hp : Tendsto (Pool.weightedQueryProbability π ∘ Q.position) atTop (𝓝 pstar))
    (S : Set ℕ) (hS : ∀ᶠ n in atTop, Q.position n ∈ S) :
    ∀ᶠ M in atTop, ∃ C, Accepted P.rules P.advice M C ∧ ∀ b ∈ C.1, b ∈ S := by
  have hπ : ∀ i < P.rules.length, P.rules[i]? = some (π i) := by
    intro i hi
    exact P.getElem?_rules (by simpa only [P.length_rules] using hi)
  filter_upwards [Q.eventually_exists_final_pool_in ha P.advice.protectedCount
    P.rules.length P.advice.positionBound P.error_real_pos
    (P.eventually_weighted_above hp) S hS] with M hM
  obtain ⟨G, hcard, hGS, hposition, hGhigh, hGdist, hGweighted⟩ := hM
  have haccept : ∃ V, Accepted P.rules P.advice M (G.toList, V) := by
    apply exists_accepted_on_pool hπ P.advice P.protected_le_length P.error_real_pos
      hcard hposition (hweighted := hGweighted)
    · intro i hi
      have hi' : i < ℓ := by rwa [P.protected_eq] at hi
      have hsub : {Z | Z ∈ highSet P.advice i ∧ PoolQuery.readFraction (π i) G Z < 1} ⊆
          (Q.high i ∆ highSet P.advice i) ∪
            {Z | Z ∈ Q.high i ∧ PoolQuery.readFraction (π i) G Z < 1} := by
        intro Z hZ
        by_cases hz : Z ∈ Q.high i
        · exact Or.inr ⟨hz, hZ.2⟩
        · exact Or.inl (Or.inr ⟨hZ.1, hz⟩)
      have hle := (measureReal_mono hsub (measure_ne_top fairCoin _)).trans
        (measureReal_union_le (μ := fairCoin) _ _)
      linarith [P.high_approx i hi', hGhigh i hi]
    · intro i hi
      have hi' : i < ℓ := by rwa [P.protected_eq] at hi
      have hrep : Integrable (Q.representative i) fairCoin :=
        (Pool.integrable_L2 (Q.limit i)).congr (Q.representative_ae_eq i).symm
      have htri := PoolSoundness.integral_abs_sub_le_add
        (PoolQuery.integrable_readFraction (π i) G) hrep (integrable_approx P.advice i)
      have happ : (∫ Z, |Q.representative i Z - approx P.advice i Z| ∂fairCoin) <
          (P.advice.error : ℝ) := by
        simpa only [abs_sub_comm] using P.function_approx i hi'
      linarith [hGdist i hi]
  obtain ⟨V, hV⟩ := haccept
  exact ⟨(G.toList, V), hV, fun b hb => hGS b (Finset.mem_toList.mp hb)⟩

end Parameters

/-- Fixed weak-limit partitions yield ordinary computable pools when c.e.
reservoirs provide arbitrarily close local weighted upper bounds. No global
weighted-limsup maximization is required. -/
theorem exists_computable_pools_of_reservoirs {π : ℕ → ScanRule} {a : ℕ → ℕ}
    (Q : Pool.QueryPartition π a) (ha : Tendsto Q.position atTop atTop)
    {pstar : ℝ}
    (hp : Tendsto (Pool.weightedQueryProbability π ∘ Q.position) atTop (𝓝 pstar))
    (hreservoir : ∀ ε : ℝ, 0 < ε → ∃ S : Set ℕ,
      REPred (fun b => b ∈ S) ∧ (∀ᶠ n in atTop, Q.position n ∈ S) ∧
      ∀ b ∈ S, Pool.weightedQueryProbability π b ≤ pstar + ε) :
    ∀ (ℓ : ℕ) (η : ℝ), 0 < η → ∀ z : ℕ,
      ∃ τ : ℚ, 0 < τ ∧ τ < 1 / 4 ∧
        ∃ e : Nat.Partrec.Code, ∀ᶠ M : ℕ in atTop,
          ∃ G : List ℕ, encodePool G ∈ e.eval M ∧
            PoolConstruction.GoodPool π Q.high ℓ η z τ M G := by
  intro ℓ η hη z
  obtain ⟨P⟩ := exists_parameters Q ℓ hη z pstar
  obtain ⟨S, hS, hmem, hupper⟩ := hreservoir
    (protectedWeight P.advice * (P.advice.error : ℝ)) P.slack_pos
  have hne : S.Nonempty := by
    obtain ⟨n, hn⟩ := hmem.exists
    exact ⟨Q.position n, hn⟩
  obtain ⟨f, hf, hrange⟩ := exists_primrec_range hS hne
  have haccepted : ∀ᶠ M in atTop, ∃ C, Accepted P.rules P.advice M C ∧
      ∀ b ∈ C.1, b ∈ Set.range f := by
    simpa only [hrange] using P.eventually_accepted_in ha hp S hmem
  obtain ⟨e, he⟩ := exists_eventual_program P.rules P.advice hf haccepted
  have hpstar : 0 ≤ pstar := ge_of_tendsto' hp
    (fun n => Pool.weightedQueryProbability_nonneg π (Q.position n))
  refine ⟨P.margin, P.margin_pos, P.margin_lt_quarter, e, ?_⟩
  filter_upwards [he] with M hM
  obtain ⟨G, V, hcode, hC, hG⟩ := hM
  refine ⟨G, hcode, P.goodPool_of_accepted hC hpstar ?_⟩
  intro b hb
  exact hupper b (hrange ▸ hG b hb)

end Klr.PoolReservoir
