module

public import Klr.LeftCeReservoir
public import Klr.Computability.CauchyModulus
public import Klr.Computability.OracleRecursion

/-!
# Second-jump selection of finite coordinate refinements

The state consists of a stage counter and one finite lower-bound reservoir.
A refinement confines the scheduled coordinate to a short rational interval,
raises the cutoff, and makes the cutoff itself a member of the new reservoir.
Both the actual witness selector and its computability in the second jump are
proved from the lower names; no effective compactness principle is assumed.
-/

@[expose] public section

namespace Klr.CoordinateRefinement

open Klr.Computability Klr.Computability.ArithmeticHierarchy
open Klr.Computability.OracleJump Klr.LeftCeReservoir RationalComputability
open Encodable

local instance : Encodable ℚ := (inferInstance : Primcodable ℚ).toEncodable

abbrev State := ℕ × Reservoir
abbrev Candidate := ℚ × ℚ × ℕ

def readState (v : ℕ) : State := (Encodable.decode v).getD (0, 0, [])
def readCandidate (v : ℕ) : Candidate := (Encodable.decode v).getD (0, 0, 0)

theorem readState_primrec : Primrec readState :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const (0, 0, []))

theorem readCandidate_primrec : Primrec readCandidate :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const (0, 0, 0))

@[simp] theorem readState_encode (s : State) : readState (encode s) = s := by
  simp [readState]

@[simp] theorem readCandidate_encode (w : Candidate) : readCandidate (encode w) = w := by
  simp [readCandidate]

def lower (s : State) (w : Candidate) : Reservoir :=
  cut s.2 (Nat.unpair s.1).1 w.1 w.2.2

def upper (s : State) (w : Candidate) : Reservoir :=
  cut s.2 (Nat.unpair s.1).1 w.2.1 w.2.2

def Bounds (s : State) (w : Candidate) : Prop :=
  s.2.1 < w.2.2 ∧ 0 < w.2.1 - w.1 ∧
    w.2.1 - w.1 < CauchyModulus.dyadic (Nat.unpair s.1).2

def Good (f : ℕ → ℕ → ℝ) (s : State) (w : Candidate) : Prop :=
  Bounds s w ∧ Unbounded f (lower s w) ∧
    (∀ n, ¬ Contains f (upper s w) n) ∧ Contains f (lower s w) w.2.2

def Valid (f : ℕ → ℕ → ℝ) (v : ℕ) : Prop := Unbounded f (readState v).2

def advance (s : State) (w : Candidate) : State := (s.1 + 1, lower s w)

def nextCode (v w : ℕ) : ℕ := encode (advance (readState v) (readCandidate w))

theorem cut_primrec {α : Type*} [Primcodable α]
    {R : α → Reservoir} {i b : α → ℕ} {l : α → ℚ}
    (hR : Primrec R) (hi : Primrec i) (hl : Primrec l) (hb : Primrec b) :
    Primrec (fun a => cut (R a) (i a) (l a) (b a)) :=
  (Primrec.nat_max.comp (Primrec.fst.comp hR) hb).pair
    (Primrec.list_cons.comp (hi.pair hl) (Primrec.snd.comp hR))

theorem lower_primrec : Primrec₂ lower :=
  cut_primrec (Primrec.snd.comp Primrec.fst)
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.fst)))
    (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

theorem upper_primrec : Primrec₂ upper :=
  cut_primrec (Primrec.snd.comp Primrec.fst)
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.fst)))
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

theorem advance_primrec : Primrec₂ advance :=
  (Primrec.succ.comp (Primrec.fst.comp Primrec.fst)).pair lower_primrec

theorem nextCode_primrec : Primrec₂ nextCode :=
  Primrec.encode.comp (advance_primrec.comp
    (readState_primrec.comp Primrec.fst) (readCandidate_primrec.comp Primrec.snd))

private theorem primrec_rat_lt : PrimrecRel (fun a b : ℚ => a < b) :=
  (primrec_rat_le.comp Primrec.snd Primrec.fst).not.of_eq (fun _ => not_le)

theorem bounds_primrec : PrimrecPred (fun p : State × Candidate => Bounds p.1 p.2) := by
  have hl : Primrec (fun p : State × Candidate => p.2.1) := Primrec.fst.comp Primrec.snd
  have hu : Primrec (fun p : State × Candidate => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hw := primrec_rat_sub.comp hu hl
  exact (Primrec.nat_lt.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).and
    ((primrec_rat_lt.comp (Primrec.const 0) hw).and
      (primrec_rat_lt.comp hw (CauchyModulus.primrec_dyadic.comp
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.fst))))))

private theorem recursive_primrecPred {A : Oracle} {P : ℕ → Prop}
    (h : PrimrecPred P) : RecursivePred A P := by
  classical
  exact Form.congr (n := 0) (s := true) (CeCofinality.recursive_bool h.decide.to_comp)
    (fun _ => by simp)

variable {f : ℕ → ℕ → ℝ} (D : LowerName f)

include D

theorem valid_recursive : RecursivePred (zeroJump 2) (Valid f) := by
  have hr : Primrec (fun v => encode (readState v).2) :=
    Primrec.encode.comp (Primrec.snd.comp readState_primrec)
  have h := recursive_comp D.unbounded_recursive hr
  apply Form.congr (n := 0) (s := true) h
  intro v
  simp only [decode_encode, Valid]

theorem good_recursive : RecursivePred (zeroJump 2) (fun z =>
    Good f (readState (Nat.unpair z).1) (readCandidate (Nat.unpair z).2)) := by
  let l := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hs := readState_primrec.comp l
  have hw := readCandidate_primrec.comp r
  have hlow := lower_primrec.comp hs hw
  have hupp := upper_primrec.comp hs hw
  have hN := Primrec.snd.comp (Primrec.snd.comp hw)
  have hb := recursive_primrecPred (A := zeroJump 2) (bounds_primrec.comp (hs.pair hw))
  have hc := recursive_comp D.unbounded_recursive (Primrec.encode.comp hlow)
  have he := recursive_comp D.empty_recursive (Primrec.encode.comp hupp)
  have hm := recursive_comp D.contains_recursive
    (Primrec₂.natPair.comp (Primrec.encode.comp hlow) hN)
  have h := recursive_and hb (recursive_and hc (recursive_and he hm))
  simpa only [Nat.unpair_pair, decode_encode, Good] using h

omit D in
/-- Every valid reservoir admits a genuine next refinement. -/
theorem exists_good (hf0 : ∀ i n, 0 ≤ f i n) (hf1 : ∀ i n, f i n ≤ 1)
    {s : State} (hs : Unbounded f s.2) : ∃ w : Candidate, Good f s w := by
  have hε : (0 : ℝ) < CauchyModulus.dyadic (Nat.unpair s.1).2 := by
    exact_mod_cast pow_pos (by norm_num : (0 : ℚ) < 1 / 2) (Nat.unpair s.1).2
  obtain ⟨l, u, N, hwidth, hsmall, hN, hcof, hemp⟩ :=
    exists_interval_refinement hf0 hf1 hs (Nat.unpair s.1).1 s.2.1 hε
  obtain ⟨n, hn, hmem⟩ := hcof N
  have hnold : s.2.1 < n := hN.trans_le hn
  have hc : Unbounded f (cut s.2 (Nat.unpair s.1).1 l n) := by
    intro b
    obtain ⟨m, hm, hRm⟩ := hcof (max b n)
    obtain ⟨hOld, _, hl⟩ := contains_cut.mp hRm
    exact ⟨m, (Nat.le_max_left _ _).trans hm,
      contains_cut.mpr ⟨hOld, (Nat.le_max_right _ _).trans hm, hl⟩⟩
  have he : ∀ m, ¬ Contains f (cut s.2 (Nat.unpair s.1).1 u n) m := by
    intro m hm
    obtain ⟨hOld, hnm, hu⟩ := contains_cut.mp hm
    exact hemp m (contains_cut.mpr ⟨hOld, hn.trans hnm, hu⟩)
  have hm : Contains f (cut s.2 (Nat.unpair s.1).1 l n) n := by
    obtain ⟨hOld, _, hl⟩ := contains_cut.mp hmem
    exact contains_cut.mpr ⟨hOld, le_rfl, hl⟩
  refine ⟨(l, u, n), ⟨hnold, hwidth, ?_⟩, hc, he, hm⟩
  exact_mod_cast hsmall

/-- The second jump computes an actual refinement witness on every valid
input. Invalid numerical states are assigned arbitrary outputs. -/
theorem exists_selector (hf0 : ∀ i n, 0 ≤ f i n) (hf1 : ∀ i n, f i n ≤ 1) :
    ∃ choose : ℕ → ℕ,
      Nat.RecursiveIn {oracleFunction (zeroJump 2)} (fun v => Part.some (choose v)) ∧
      ∀ v, Valid f v → Good f (readState v) (readCandidate (choose v)) := by
  let P : ℕ → Prop := fun z =>
    ¬ Valid f (Nat.unpair z).1 ∨
      Good f (readState (Nat.unpair z).1) (readCandidate (Nat.unpair z).2)
  have hP : RecursivePred (zeroJump 2) P :=
    Form.or (n := 0) (s := true)
      (recursive_not (recursive_comp (valid_recursive D) (Primrec.fst.comp Primrec.unpair)))
      (good_recursive D)
  have htotal : ∀ v, ∃ w, P (Nat.pair v w) := by
    intro v
    classical
    by_cases hv : Valid f v
    · obtain ⟨w, hw⟩ := exists_good hf0 hf1 hv
      exact ⟨encode w, by simpa only [P, Nat.unpair_pair, readCandidate_encode] using Or.inr hw⟩
    · exact ⟨0, by simp only [P, Nat.unpair_pair, hv, not_false_eq_true, true_or]⟩
  refine ⟨ArithmeticSelection.least P htotal,
    ArithmeticSelection.least_recursive hP htotal, fun v hv => ?_⟩
  have h := ArithmeticSelection.least_spec P htotal v
  simpa only [P, Nat.unpair_pair, hv, not_true_eq_false, false_or] using h

end Klr.CoordinateRefinement
