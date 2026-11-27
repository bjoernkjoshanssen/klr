module

public import Klr.FiniteStageCandidate
public import Klr.StageFiniteScan

/-!
# Finite histories of coded affine stages

A history is an ordinary finite list of finite candidates. Its decoded
blocks and horizons have explicit empty padding. The executable cutoff
bounds every old pool and every protected scan branch, and is larger than
the history length; hence the next stage can also move beyond its index.
-/

@[expose] public section

namespace Klr.FiniteStageHistory

open FiniteStageCandidate SparseSearch

abbrev History := List Candidate

noncomputable def blocks (h : History) (k : ℕ) : AffineBlock :=
  (h[k]?).elim StageRecursion.emptyBlock FiniteStageCandidate.block

def horizons (h : History) (k : ℕ) : ℕ := horizon (h.getD k default)

def codes (h : History) : List AffineCode.Data := h.map output

@[simp] theorem blocks_get (h : History) (k : ℕ) (hk : k < h.length) :
    blocks h k = FiniteStageCandidate.block h[k] := by
  simp [blocks, hk]

theorem blocks_getD (h : History) (k : ℕ) (hk : k < h.length) :
    blocks h k = FiniteStageCandidate.block (h.getD k default) := by
  simp [blocks, List.getD_eq_getElem?_getD, hk]

@[simp] theorem blocks_tail (h : History) (k : ℕ) (hk : h.length ≤ k) :
    blocks h k = StageRecursion.emptyBlock := by
  simp [blocks, List.getElem?_eq_none hk]

@[simp] theorem horizons_tail (h : History) (k : ℕ) (hk : h.length ≤ k) :
    horizons h k = 0 := by
  simp only [horizons, List.getD_eq_getElem?_getD, List.getElem?_eq_none hk, Option.getD_none]
  rfl

theorem computable_horizons : Computable₂ horizons :=
  primrec_horizon.to_comp.comp (Primrec.list_getD (default : Candidate)).to_comp

theorem primrec_codes : Primrec codes :=
  Primrec.list_map Primrec.id (primrec_output.comp Primrec.snd).to₂

/-- The old semantic history interface is obtained without choosing any matrices. -/
noncomputable def decode (h : History)
    (hd : Pairwise (fun i j => Disjoint (blocks h i).support (blocks h j).support)) :
    StageRecursion.History h.length where
  blocks := blocks h
  horizon := horizons h
  disjoint := hd
  blocks_tail := blocks_tail h
  horizon_tail := horizons_tail h

/-- The finite invariant needed by candidate search: genuine disjoint blocks
and correctly checked output descriptions at their own stage indices. -/
structure Valid (h : History) : Prop where
  disjoint : Pairwise (fun i j => Disjoint (blocks h i).support (blocks h j).support)
  checked : ∀ j (hj : j < h.length), Checked j 0 h[j]

theorem valid_empty : Valid [] := by
  refine ⟨?_, ?_⟩
  · intro i j hij
    simp [blocks, StageRecursion.emptyBlock]
  · intro j hj
    simp at hj

/-- Appending a candidate changes just the next padded block. -/
theorem blocks_append (h : History) (c : Candidate) :
    blocks (h ++ [c]) = Function.update (blocks h) h.length (FiniteStageCandidate.block c) := by
  funext k
  by_cases hk : k < h.length
  · simp [blocks, List.getElem?_append_left hk, Function.update_of_ne (Nat.ne_of_lt hk)]
  · have hle : h.length ≤ k := Nat.le_of_not_gt hk
    rw [show k = h.length + (k - h.length) from (Nat.add_sub_of_le hle).symm]
    cases he : k - h.length with
    | zero => simp [blocks]
    | succ j =>
      have hne : h.length + (j + 1) ≠ h.length := by omega
      simp [blocks]

/-- The horizon array has the same exact append behavior. -/
theorem horizons_append (h : History) (c : Candidate) :
    horizons (h ++ [c]) = Function.update (horizons h) h.length (horizon c) := by
  funext k
  by_cases hk : k < h.length
  · simp [horizons, List.getD_eq_getElem?_getD, List.getElem?_append_left hk,
      Function.update_of_ne (Nat.ne_of_lt hk)]
  · have hle : h.length ≤ k := Nat.le_of_not_gt hk
    rw [show k = h.length + (k - h.length) from (Nat.add_sub_of_le hle).symm]
    cases he : k - h.length with
    | zero => simp [horizons, List.getD_eq_getElem?_getD]
    | succ j =>
      have hne : h.length + (j + 1) ≠ h.length := by omega
      simp [horizons, List.getD_eq_getElem?_getD]

/-- A uniformly computable dispatcher computes all its finite branch bounds. -/
theorem computable_branchBound (π : ℕ → ScanRule)
    (hπ : Computable (fun p : ℕ × List Bool => (π p.1).query p.2)) :
    Computable₂ (fun i V => StageFiniteScan.branchBound (π i) V) := by
  have hi : Computable (fun p : ℕ × ℕ =>
      ((words p.2).map (fun v => (π p.1).query v + 1)).sum) :=
    StageFiniteScan.computable_list_sum (computable_words.comp Computable.snd)
      (Primrec.succ.to_comp.comp (hπ.comp
        ((Computable.fst.comp Computable.fst).pair Computable.snd)))
  have ht : Computable₂ (fun p : ℕ × ℕ => fun t =>
      ((words t).map (fun v => (π p.1).query v + 1)).sum) :=
    (hi.comp ((Computable.fst.comp Computable.fst).pair Computable.snd)).to₂
  exact (StageFiniteScan.computable_list_sum
    (l := fun p : ℕ × ℕ => List.range p.2)
    (Primrec.list_range.to_comp.comp Computable.snd) ht).of_eq fun _ => rfl

def branchSum (π : ℕ → ScanRule) (j V : ℕ) : ℕ :=
  ((List.range (j + 1)).map (fun i => StageFiniteScan.branchBound (π i) V + 1)).sum

def term (π : ℕ → ScanRule) (h : History) (j : ℕ) : ℕ :=
  FiniteStageData.bound (data (h.getD j default)) + branchSum π j (horizons h j)

def cutoff (π : ℕ → ScanRule) (h : History) : ℕ :=
  ((List.range h.length).map (term π h)).sum + h.length + 1

theorem computable_branchSum (π : ℕ → ScanRule)
    (hπ : Computable (fun p : ℕ × List Bool => (π p.1).query p.2)) :
    Computable₂ (branchSum π) := by
  have hv : Computable (fun p : (ℕ × ℕ) × ℕ =>
      StageFiniteScan.branchBound (π p.2) p.1.2) :=
    (computable_branchBound π hπ).comp Computable.snd (Computable.snd.comp Computable.fst)
  exact StageFiniteScan.computable_list_sum
    (Primrec.list_range.to_comp.comp (Computable.succ.comp Computable.fst))
    (Primrec.succ.to_comp.comp hv)

theorem computable_term (π : ℕ → ScanRule)
    (hπ : Computable (fun p : ℕ × List Bool => (π p.1).query p.2)) :
    Computable₂ (term π) := by
  have hb := FiniteStageData.computable_bound.comp
    (primrec_data.to_comp.comp (Primrec.list_getD (default : Candidate)).to_comp)
  exact Primrec.nat_add.to_comp.comp hb
    ((computable_branchSum π hπ).comp Computable.snd computable_horizons)

theorem computable_cutoff (π : ℕ → ScanRule)
    (hπ : Computable (fun p : ℕ × List Bool => (π p.1).query p.2)) :
    Computable (cutoff π) := by
  have hs := StageFiniteScan.computable_list_sum
    (Primrec.list_range.to_comp.comp Computable.list_length) (computable_term π hπ)
  exact Primrec.succ.to_comp.comp
    (Primrec.nat_add.to_comp.comp hs Computable.list_length)

theorem term_lt_cutoff (π : ℕ → ScanRule) (h : History) {j : ℕ} (hj : j < h.length) :
    term π h j < cutoff π h := by
  have ht : term π h j ≤ ((List.range h.length).map (term π h)).sum :=
    List.le_sum_of_mem (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
  unfold cutoff
  omega

theorem length_lt_cutoff (π : ℕ → ScanRule) (h : History) : h.length < cutoff π h := by
  unfold cutoff
  omega

/-- This bounds all old coordinates, including unused positions in their pools. -/
theorem pool_lt_cutoff (π : ℕ → ScanRule) (h : History) {j p : ℕ}
    (hj : j < h.length) (hp : p ∈ FiniteStageData.pool (data (h.getD j default))) :
    p < cutoff π h := by
  have hb : p < FiniteStageData.bound (data (h.getD j default)) :=
    Nat.lt_succ_of_le (List.le_sum_of_mem hp)
  have ht := term_lt_cutoff π h hj
  unfold term at ht
  omega

theorem support_lt_cutoff (π : ℕ → ScanRule) (h : History) {j p : ℕ}
    (hj : j < h.length) (hp : p ∈ (blocks h j).support) : p < cutoff π h := by
  rw [blocks_getD h j hj] at hp
  exact pool_lt_cutoff π h hj (List.mem_toFinset.mp (FiniteStageData.support_subset_pool _ hp))

/-- The historical max-based query bound is below the executable branch sum. -/
theorem queryBound_le_branchBound (π : ScanRule) (V : ℕ) :
    HorizonAvoidance.queryBound π V ≤ StageFiniteScan.branchBound π V + 1 := by
  apply Nat.succ_le_succ
  apply Finset.sup_le
  intro q hq
  obtain ⟨v, hv, rfl⟩ := (HorizonAvoidance.mem_queryPositions π V q).mp hq
  exact (StageFiniteScan.query_lt_branchBound π V v hv).le

theorem queryBound_le_cutoff (π : ℕ → ScanRule) (h : History) {j : ℕ}
    (hj : j < h.length) (i : ℕ) (hi : i ≤ j) :
    HorizonAvoidance.queryBound (π i) (horizons h j) ≤ cutoff π h := by
  have hs : StageFiniteScan.branchBound (π i) (horizons h j) + 1 ≤
      branchSum π j (horizons h j) :=
    List.le_sum_of_mem (List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩)
  have ht := term_lt_cutoff π h hj
  have hq := queryBound_le_branchBound (π i) (horizons h j)
  unfold term at ht
  omega

/-- A support above the executable cutoff is disjoint from all old blocks. -/
theorem disjoint_of_above (π : ℕ → ScanRule) (h : History) (C : AffineBlock)
    (hC : ∀ p ∈ C.support, cutoff π h ≤ p) (j : ℕ) :
    Disjoint (blocks h j).support C.support := by
  by_cases hj : j < h.length
  · apply Finset.disjoint_left.mpr
    intro p hp hpC
    exact (not_lt_of_ge (hC p hpC)) (support_lt_cutoff π h hj hp)
  · rw [blocks_tail h j (Nat.le_of_not_gt hj)]
    simp

theorem Valid.append {h : History} (hv : Valid h) (π : ℕ → ScanRule) {c : Candidate}
    (hc : check h.length (cutoff π h) c = true) : Valid (h ++ [c]) := by
  have hs := check_sound hc
  refine ⟨?_, ?_⟩
  · rw [blocks_append]
    intro i j hij
    by_cases hi : i = h.length
    · subst i
      have hj : j ≠ h.length := Ne.symm hij
      simpa only [Function.update_self, Function.update_of_ne hj] using
        (disjoint_of_above π h (FiniteStageCandidate.block c) hs.above j).symm
    · by_cases hj : j = h.length
      · subst j
        simpa only [Function.update_self, Function.update_of_ne hi] using
          disjoint_of_above π h (FiniteStageCandidate.block c) hs.above i
      · simpa only [Function.update_of_ne hi, Function.update_of_ne hj] using hv.disjoint hij
  · intro j hj
    by_cases hjh : j < h.length
    · simpa only [List.getElem_append_left hjh] using hv.checked j hjh
    · have he : j = h.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      subst j
      have hzero : Checked h.length 0 c :=
        ⟨hs.valid, fun _ _ => Nat.zero_le _, hs.output_valid, hs.rank,
          hs.event, hs.budget, hs.runs⟩
      simpa using hzero

theorem blocks_take (h : History) (a k : ℕ) (hk : k < a) :
    blocks (h.take a) k = blocks h k := by
  simp only [blocks, List.getElem?_take_of_lt hk]

theorem Valid.take {h : History} (hv : Valid h) (a : ℕ) : Valid (h.take a) := by
  refine ⟨?_, ?_⟩
  · intro i j hij
    by_cases hi : i < (h.take a).length
    · by_cases hj : j < (h.take a).length
      · have hia : i < a := (List.length_take_le a h).trans_lt' hi
        have hja : j < a := (List.length_take_le a h).trans_lt' hj
        rw [blocks_take h a i hia, blocks_take h a j hja]
        exact hv.disjoint hij
      · rw [blocks_tail _ _ (Nat.le_of_not_gt hj)]
        simp
    · rw [blocks_tail _ _ (Nat.le_of_not_gt hi)]
      simp
  · intro j hj
    have hjh : j < h.length := by
      simp only [List.length_take] at hj
      omega
    simpa using hv.checked j hjh

/-- Checked output events describe exactly the decoded finite block prefix. -/
theorem event_codes {h : History} (hv : Valid h) :
    StageFiniteProbability.event (codes h) = PrefixStage.prefixEvent (blocks h) h.length := by
  ext X
  rw [PrefixStage.mem_prefixEvent]
  constructor
  · intro hx j hj
    have hm : output h[j] ∈ codes h := List.mem_map.mpr ⟨h[j], List.getElem_mem hj, rfl⟩
    have he := (hv.checked j hj).event
    have ht := hx _ hm
    rw [he] at ht
    simpa only [blocks_get h j hj] using ht
  · intro hx c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hd
    rw [(hv.checked j hj).event]
    simpa only [blocks_get h j hj] using hx j hj

theorem law_codes {h : History} (hv : Valid h) :
    StageFiniteProbability.law (codes h) = PrefixStage.law (blocks h) h.length := by
  rw [StageFiniteProbability.law, PrefixStage.law_eq_cond, event_codes hv]

/-- Every earlier finite code header has exactly the corresponding old law. -/
theorem law_codes_take {h : History} (hv : Valid h) (a : ℕ) (ha : a ≤ h.length) :
    StageFiniteProbability.law (codes (h.take a)) = PrefixStage.law (blocks h) a := by
  rw [law_codes (hv.take a), List.length_take, Nat.min_eq_left ha]
  apply congrArg AffineBlock.finiteStageLaw
  funext i
  exact blocks_take h a i.val i.isLt

end Klr.FiniteStageHistory
