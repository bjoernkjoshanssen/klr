module

public import Klr.Computability.CeCofinality
public import Klr.ComputableRational
public import Klr.SparseSearchRank

/-!
# Finite reservoirs for left-c.e. coordinates

A reservoir is a tail of the natural numbers restricted by finitely many
strict lower bounds on left-c.e. real coordinates. It is still computably
enumerable. Cofinality and emptiness of these reservoirs can be decided in
the second jump, uniformly in their finite codes.

An infinite reservoir can be refined so that one bounded coordinate lies in
an arbitrarily short rational interval. The upper bound is enforced by
discarding a finite initial segment, so the refined reservoir still has a
positive, computably enumerable membership test.
-/

@[expose] public section

namespace Klr.LeftCeReservoir

open Klr.Computability Klr.Computability.ArithmeticHierarchy Klr.Computability.OracleJump
open RationalComputability Encodable

local instance : Encodable ℚ := (inferInstance : Primcodable ℚ).toEncodable

abbrev Reservoir := ℕ × List (ℕ × ℚ)

def Contains (f : ℕ → ℕ → ℝ) (R : Reservoir) (n : ℕ) : Prop :=
  R.1 ≤ n ∧ ∀ c ∈ R.2, (c.2 : ℝ) < f c.1 n

def Unbounded (f : ℕ → ℕ → ℝ) (R : Reservoir) : Prop :=
  ∀ b, ∃ n, b ≤ n ∧ Contains f R n

def cut (R : Reservoir) (i : ℕ) (l : ℚ) (b : ℕ) : Reservoir :=
  (max R.1 b, (i, l) :: R.2)

theorem contains_cut {f : ℕ → ℕ → ℝ} {R : Reservoir} {i b n : ℕ} {l : ℚ} :
    Contains f (cut R i l b) n ↔ Contains f R n ∧ b ≤ n ∧ (l : ℝ) < f i n := by
  simp only [Contains, cut, max_le_iff, List.mem_cons, Prod.forall, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hr, hb⟩, h⟩
    exact ⟨⟨hr, fun j q hc => h j q (Or.inr hc)⟩, hb, h i l (Or.inl ⟨rfl, rfl⟩)⟩
  · rintro ⟨⟨hr, h⟩, hb, hl⟩
    refine ⟨⟨hr, hb⟩, fun j q hc => ?_⟩
    rcases hc with ⟨rfl, rfl⟩ | hc
    · exact hl
    · exact h j q hc

/-- A uniformly computable increasing rational lower name. -/
structure LowerName (f : ℕ → ℕ → ℝ) where
  approx : ℕ → ℕ → ℕ → ℚ
  computable : Computable (fun z : ℕ × ℕ × ℕ => approx z.1 z.2.1 z.2.2)
  monotone : ∀ i n, Monotone (approx i n)
  sound : ∀ i n t, (approx i n t : ℝ) ≤ f i n
  complete : ∀ i n (r : ℚ), (r : ℝ) < f i n → ∃ t, r < approx i n t

namespace LowerName

variable {f : ℕ → ℕ → ℝ} (D : LowerName f)

include D

def test (R : Reservoir) (n t : ℕ) : Bool :=
  decide (R.1 ≤ n) && R.2.all (fun c => decide (c.2 < D.approx c.1 n t))

theorem contains_iff (R : Reservoir) (n : ℕ) :
    Contains f R n ↔ ∃ t, D.test R n t = true := by
  have hfinite : ∀ L : List (ℕ × ℚ),
      (∀ c ∈ L, (c.2 : ℝ) < f c.1 n) →
      ∃ t, ∀ c ∈ L, c.2 < D.approx c.1 n t := by
    intro L
    induction L with
    | nil => exact fun _ => ⟨0, by simp⟩
    | cons c L ih =>
      intro h
      obtain ⟨t, ht⟩ := D.complete c.1 n c.2 (h c (by simp))
      obtain ⟨s, hs⟩ := ih (fun d hd => h d (by simp [hd]))
      refine ⟨max t s, fun d hd => ?_⟩
      rcases List.mem_cons.mp hd with rfl | hd
      · exact ht.trans_le (D.monotone _ _ (Nat.le_max_left _ _))
      · exact (hs d hd).trans_le (D.monotone _ _ (Nat.le_max_right _ _))
  constructor
  · rintro ⟨hR, hL⟩
    obtain ⟨t, ht⟩ := hfinite R.2 hL
    exact ⟨t, by simpa [test, hR, List.all_eq_true] using ht⟩
  · rintro ⟨t, ht⟩
    simp only [test, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ht
    refine ⟨ht.1, fun c hc => ?_⟩
    have hq : c.2 < D.approx c.1 n t := by simpa using ht.2 c hc
    exact (show (c.2 : ℝ) < D.approx c.1 n t by exact_mod_cast hq).trans_le
      (D.sound _ _ _)

omit D in
private theorem primrec_rat_lt : PrimrecRel (fun a b : ℚ => a < b) :=
  (primrec_rat_le.comp Primrec.snd Primrec.fst).not.of_eq (fun _ => not_le)

theorem test_computable :
    Computable (fun z : Reservoir × ℕ × ℕ => D.test z.1 z.2.1 z.2.2) := by
  have hp : Computable₂ (fun z : Reservoir × ℕ × ℕ => fun c : ℕ × ℚ =>
      decide (c.2 < D.approx c.1 z.2.1 z.2.2)) :=
    (primrec_rat_lt.decide.to_comp.comp (Computable.snd.comp Computable.snd)
      (D.computable.comp ((Computable.fst.comp Computable.snd).pair
        ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
          (Computable.snd.comp (Computable.snd.comp Computable.fst)))))).to₂
  exact Primrec.and.to_comp.comp
    (Primrec.nat_le.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)).decide.to_comp
    (SparseSearch.computable_list_all (Computable.snd.comp Computable.fst) hp)

theorem contains_re (R : Reservoir) : REPred (Contains f R) := by
  have hc : Computable (fun z : ℕ × ℕ => decide (D.test R z.1 z.2 = true)) := by
    simpa using D.test_computable.comp ((Computable.const R).pair Computable.id)
  exact (rePred_exists hc.computablePred.to_re).of_eq
    (fun n => (D.contains_iff R n).symm)

end LowerName

def decode (r : ℕ) : Reservoir := (Encodable.decode r).getD (0, [])

@[simp] theorem decode_encode (R : Reservoir) : decode (encode R) = R := by
  simp [decode]

theorem decode_primrec : Primrec decode :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const (0, []))

namespace LowerName

variable {f : ℕ → ℕ → ℝ} (D : LowerName f)

include D

def enumerator (r n t : ℕ) : Bool := D.test (decode r) n t

theorem enumerator_computable :
    Computable (fun z : ℕ × ℕ × ℕ => D.enumerator z.1 z.2.1 z.2.2) := by
  have hd : Computable (fun z : ℕ × ℕ × ℕ => decode z.1) :=
    decode_primrec.to_comp.comp Computable.fst
  have hi : Computable (fun z : ℕ × ℕ × ℕ => (decode z.1, z.2)) :=
    hd.pair Computable.snd
  have hc := D.test_computable.comp hi
  simpa only [enumerator] using hc

theorem unbounded_iff (r : ℕ) :
    Unbounded f (decode r) ↔ CeCofinality.Cofinal D.enumerator r := by
  simp only [Unbounded, CeCofinality.Cofinal, CeCofinality.Member,
    D.contains_iff, enumerator]

theorem unbounded_recursive :
    RecursivePred (zeroJump 2) (fun r => Unbounded f (decode r)) :=
  Form.congr (n := 0) (s := true)
    (CeCofinality.cofinal_recursive D.enumerator_computable)
    (fun r => (D.unbounded_iff r).symm)

theorem contains_recursive :
    RecursivePred (zeroJump 2) (fun v =>
      Contains f (decode (Nat.unpair v).1) (Nat.unpair v).2) := by
  apply Form.congr (n := 0) (s := true)
    (CeCofinality.member_recursive_two D.enumerator_computable)
  intro v
  exact (D.contains_iff _ _).symm

theorem empty_recursive :
    RecursivePred (zeroJump 2) (fun r => ∀ n, ¬ Contains f (decode r) n) := by
  apply Form.congr (n := 0) (s := true)
    (CeCofinality.empty_recursive_two D.enumerator_computable)
  intro r
  simp only [CeCofinality.Empty, enumerator, D.contains_iff, not_exists,
    Bool.not_eq_true]

end LowerName

/-- One coordinate can be confined to a short rational interval while leaving
an infinite enumerable reservoir. Only lower tests and a finite cutoff are
added to the reservoir code. -/
theorem exists_interval_refinement {f : ℕ → ℕ → ℝ}
    (hf0 : ∀ i n, 0 ≤ f i n) (hf1 : ∀ i n, f i n ≤ 1)
    {R : Reservoir} (hR : Unbounded f R) (i b : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (l u : ℚ) (N : ℕ), 0 < u - l ∧ (u - l : ℝ) < ε ∧ b < N ∧
      Unbounded f (cut R i l N) ∧
      ∀ n, Contains f (cut R i u N) n → False := by
  classical
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  let t (k : ℕ) : ℚ := (k : ℚ) / (m + 1) - 1 / (m + 1)
  let P (k : ℕ) : Prop := ∀ B, ∃ n, B ≤ n ∧ Contains f R n ∧ (t k : ℝ) < f i n
  have ht0 : (t 0 : ℝ) < 0 := by
    have hq : t 0 < 0 := by
      dsimp [t]
      simp only [zero_div, zero_sub]
      exact neg_lt_zero.mpr (by positivity)
    exact_mod_cast hq
  have hP0 : P 0 := by
    intro B
    obtain ⟨n, hn, hRn⟩ := hR B
    exact ⟨n, hn, hRn, ht0.trans_le (hf0 i n)⟩
  have htlast : t (m + 2) = 1 := by
    dsimp [t]
    push_cast
    field_simp
    ring
  have hex : ∃ k, ¬ P k := by
    refine ⟨m + 2, fun h => ?_⟩
    obtain ⟨n, _, _, hn⟩ := h 0
    rw [htlast, Rat.cast_one] at hn
    exact (not_lt_of_ge (hf1 i n)) hn
  let k := Nat.find hex
  have hkpos : 0 < k := by
    by_contra h
    have hk : k = 0 := by omega
    have hnot : ¬ P k := Nat.find_spec hex
    exact hnot (by rw [hk]; exact hP0)
  have hprev : P (k - 1) := by
    by_contra h
    exact Nat.find_min hex (show k - 1 < Nat.find hex by change k - 1 < k; omega) h
  have hfail : ¬ P k := Nat.find_spec hex
  simp only [P, not_forall, not_exists, not_and, not_lt] at hfail
  obtain ⟨N, hN⟩ := hfail
  have hwidth : t k - t (k - 1) = 1 / (m + 1) := by
    dsimp [t]
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    push_cast
    ring
  refine ⟨t (k - 1), t k, max N (b + 1), ?_, ?_, by omega, ?_, ?_⟩
  · rw [hwidth]
    positivity
  · have he : ((t k : ℝ) - t (k - 1)) = 1 / (m + 1 : ℝ) := by
      simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_add,
        Rat.cast_natCast] using congrArg (fun q : ℚ => (q : ℝ)) hwidth
    rwa [he]
  · intro B
    obtain ⟨n, hn, hRn, hl⟩ := hprev (max B (max N (b + 1)))
    exact ⟨n, (Nat.le_max_left _ _).trans hn,
      contains_cut.mpr ⟨hRn, (Nat.le_max_right _ _).trans hn, hl⟩⟩
  · intro n hn
    obtain ⟨hRn, hcut, hu⟩ := contains_cut.mp hn
    exact (not_lt_of_ge (hN n (by omega) hRn)) hu

end Klr.LeftCeReservoir
