module

public import Klr.StageCandidateCode
public import Klr.PoolSearch
public import Klr.StageRecursionData

/-!
# Finite data for the exact affine stage blocks

The decoder uses the same sparse-list entry and pool embedding as the stage
proof. In particular, it preserves the block itself, including its support
and every rank-drop statistic, rather than only its affine event. Validity
is checked by the existing finite sparse-entry and duplicate tests.
-/

@[expose] public section

namespace Klr.FiniteStageData

open SparseListSearch SparseSearch

/-- Pool, support size, rank, sparse matrix entry, and syndrome word. -/
abbrev BlockData := List ℕ × ℕ × ℕ × Entry × List Bool

def pool (d : BlockData) : List ℕ := d.1
def supportSize (d : BlockData) : ℕ := d.2.1
def rank (d : BlockData) : ℕ := d.2.2.1
def entry (d : BlockData) : Entry := d.2.2.2.1
def syndrome (d : BlockData) : List Bool := d.2.2.2.2

theorem primrec_pool : Primrec pool := Primrec.fst
theorem primrec_supportSize : Primrec supportSize := Primrec.fst.comp Primrec.snd
theorem primrec_rank : Primrec rank := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
theorem primrec_entry : Primrec entry :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
theorem primrec_syndrome : Primrec syndrome :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

def parameters (d : BlockData) : Parameters :=
  ((pool d).length, supportSize d, rank d, 0, 0, 0)

theorem primrec_parameters : Primrec parameters :=
  (Primrec.list_length.comp primrec_pool).pair
    (primrec_supportSize.pair (primrec_rank.pair (Primrec.const (0, (0 : ℚ), (0 : ℚ)))))

def valid (d : BlockData) : Bool :=
  PoolAdvice.nodupCheck (pool d) && entryCheck (parameters d) (entry d)

theorem valid_eq_true (d : BlockData) : valid d = true ↔
    (pool d).Nodup ∧ GoodEntry (pool d).length (supportSize d) (rank d) (entry d) := by
  simp only [valid, Bool.and_eq_true, PoolAdvice.nodupCheck_eq_true, entryCheck_eq_true,
    parameters, universeSize, SparseListSearch.supportSize, rowRank]

theorem computable_valid : Computable valid :=
  Primrec.and.to_comp.comp (PoolAdvice.computable_nodupCheck.comp primrec_pool.to_comp)
    (computable_entryCheck.comp primrec_parameters.to_comp primrec_entry.to_comp)

/-- A valid code decodes to the exact block used by the original stage construction.
Malformed finite data has harmless empty-block semantics. -/
noncomputable def block (d : BlockData) : AffineBlock :=
  if h : valid d = true then
    StageCandidate.block (pool d).get ((valid_eq_true d).mp h).1.injective_get
      (entry d) ((valid_eq_true d).mp h).2 (wordVector (rank d) (syndrome d))
  else StageRecursion.emptyBlock

theorem block_of_valid (d : BlockData) (h : valid d = true) :
    block d = StageCandidate.block (pool d).get ((valid_eq_true d).mp h).1.injective_get
      (entry d) ((valid_eq_true d).mp h).2 (wordVector (rank d) (syndrome d)) := by
  simp only [block, dite_eq_left h]

/-- Every concrete sparse candidate has this finite representation. -/
theorem block_encode (G : List ℕ) (hG : G.Nodup) {m r : ℕ} (a : Entry)
    (ha : GoodEntry G.length m r a) (y : List Bool) :
    valid (G, m, r, a, y) = true ∧
      block (G, m, r, a, y) =
        StageCandidate.block G.get hG.injective_get a ha (wordVector r y) := by
  have hv : valid (G, m, r, a, y) = true := (valid_eq_true _).mpr ⟨hG, ha⟩
  exact ⟨hv, block_of_valid _ hv⟩

@[simp] theorem rank_block {d : BlockData} (h : valid d = true) :
    (block d).rank = rank d := by
  rw [block_of_valid d h]
  rfl

/-- Every active support position is a member of the finite pool. -/
theorem support_subset_pool (d : BlockData) : (block d).support ⊆ (pool d).toFinset := by
  by_cases h : valid d = true
  · rw [block_of_valid d h]
    intro p hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
    exact List.mem_toFinset.mpr (List.get_mem _ _)
  · simp [block, h, StageRecursion.emptyBlock]

/-- An ordinary finite pool bound also bounds the entire decoded support. -/
def bound (d : BlockData) : ℕ := StageCandidateCode.bound (pool d)

theorem computable_bound : Computable bound :=
  StageCandidateCode.computable_bound.comp primrec_pool.to_comp

theorem support_lt_bound (d : BlockData) {p : ℕ} (hp : p ∈ (block d).support) :
    p < bound d := by
  exact Nat.lt_succ_of_le
    (List.le_sum_of_mem (List.mem_toFinset.mp (support_subset_pool d hp)))

def above (z : ℕ) (d : BlockData) : Bool := (pool d).all fun p => decide (z ≤ p)

theorem above_eq_true (z : ℕ) (d : BlockData) : above z d = true ↔
    ∀ p ∈ pool d, z ≤ p := by
  simp only [above, List.all_eq_true, decide_eq_true_eq]

theorem computable_above : Computable₂ above :=
  SparseSearch.computable_list_all
    (primrec_pool.to_comp.comp Computable.snd)
    (Primrec.nat_le.decide.to_comp.comp
      (Computable.fst.comp Computable.fst) Computable.snd)

theorem support_above {z : ℕ} {d : BlockData} (h : above z d = true) :
    ∀ p ∈ (block d).support, z ≤ p := by
  intro p hp
  exact (above_eq_true z d).mp h p (List.mem_toFinset.mp (support_subset_pool d hp))

/-- The executable predicate for the exact decoded affine event. -/
def table (d : BlockData) (v : List Bool) : Bool :=
  StageCandidateCode.table (pool d) (entry d).2 (syndrome d) v

theorem computable_table : Computable₂ table := by
  have hG : Primrec (fun p : BlockData × List Bool => pool p.1) :=
    primrec_pool.comp Primrec.fst
  have hA : Primrec (fun p : BlockData × List Bool => (entry p.1).2) :=
    Primrec.snd.comp (primrec_entry.comp Primrec.fst)
  have hy : Primrec (fun p : BlockData × List Bool => syndrome p.1) :=
    primrec_syndrome.comp Primrec.fst
  have hv : Primrec (fun p : BlockData × List Bool => p.2) := Primrec.snd
  have hdata := ((hG.pair hA).pair hy).pair hv
  apply (StageCandidateCode.computable_table.comp hdata.to_comp).of_eq
  intro p
  rfl

theorem table_inputPrefix {d : BlockData} (h : valid d = true) (n : ℕ)
    (hn : bound d ≤ n) (X : Cantor) :
    table d (ScanRule.inputPrefix X n) = true ↔ X ∈ (block d).event := by
  rw [block_of_valid d h]
  exact StageCandidateCode.table_inputPrefix (pool d) ((valid_eq_true d).mp h).1
    (entry d) ((valid_eq_true d).mp h).2 (syndrome d) n hn X

end Klr.FiniteStageData
