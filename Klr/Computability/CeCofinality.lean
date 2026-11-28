module

public import Klr.Computability.JumpProperties

/-!
# Cofinality and emptiness of uniformly enumerable sets

An infinite reservoir of natural numbers is specified by a bounded Boolean
enumerator. Emptiness is decidable in the first jump and cofinality in the
second jump. These are the two decisions used when refining a reservoir by
strict lower bounds on left-c.e. real coordinates.
-/

@[expose] public section

namespace Klr.Computability.CeCofinality

open ArithmeticHierarchy OracleJump

/-- Membership witnessed by one successful finite enumeration stage. -/
def Member (E : ℕ → ℕ → ℕ → Bool) (r n : ℕ) : Prop := ∃ t, E r n t = true

/-- A reservoir contains arbitrarily large natural numbers. -/
def Cofinal (E : ℕ → ℕ → ℕ → Bool) (r : ℕ) : Prop :=
  ∀ b, ∃ n, b ≤ n ∧ Member E r n

/-- No finite enumeration stage succeeds. -/
def Empty (E : ℕ → ℕ → ℕ → Bool) (r : ℕ) : Prop :=
  ∀ n t, E r n t = false

theorem recursive_bool {A : Oracle} {f : ℕ → Bool} (hf : Computable f) :
    RecursivePred A (fun n => f n = true) := by
  classical
  apply (total_computable (O := {oracleFunction A})
    (bit_primrec.to_comp.comp hf)).of_eq
  intro n
  by_cases h : f n = true <;> simp [bit, h]

/-- Ordinary computable substitutions preserve relative decidability. -/
theorem recursive_comp_computable {A : Oracle} {P : ℕ → Prop}
    (hP : RecursivePred A P) {f : ℕ → ℕ} (hf : Computable f) :
    RecursivePred A (fun n => P (f n)) :=
  total_comp hP (total_computable hf)

variable {E : ℕ → ℕ → ℕ → Bool}
  (hE : Computable (fun z : ℕ × ℕ × ℕ => E z.1 z.2.1 z.2.2))

include hE

/-- Membership in the enumerable family is uniformly Σ₁. -/
theorem member_sigma_one :
    Sigma zeroOracle 1 (fun v => Member E (Nat.unpair v).1 (Nat.unpair v).2) := by
  let f := Primrec.fst.comp Primrec.unpair
  let s := Primrec.snd.comp Primrec.unpair
  have hc : Computable (fun v : ℕ =>
      E (Nat.unpair (Nat.unpair v).1).1 (Nat.unpair (Nat.unpair v).1).2
        (Nat.unpair v).2) :=
    hE.comp ((f.comp f).pair ((s.comp f).pair s)).to_comp
  have hb : Pi zeroOracle 0 (fun v =>
      E (Nat.unpair (Nat.unpair v).1).1 (Nat.unpair (Nat.unpair v).1).2
        (Nat.unpair v).2 = true) := recursive_bool hc
  apply (exists_form hb).congr
  intro v
  simp only [Nat.unpair_pair, Member]

theorem member_recursive :
    RecursivePred (zeroJump 1) (fun v => Member E (Nat.unpair v).1 (Nat.unpair v).2) :=
  form_recursive (member_sigma_one hE)

theorem member_recursive_two :
    RecursivePred (zeroJump 2) (fun v => Member E (Nat.unpair v).1 (Nat.unpair v).2) :=
  recursive_transfer (member_recursive hE) (zeroJump_mono (by decide))

/-- The cofinality predicate is uniformly Π₂, including the reservoir index. -/
theorem cofinal_pi_two : Pi zeroOracle 2 (Cofinal E) := by
  let f := Primrec.fst.comp Primrec.unpair
  let s := Primrec.snd.comp Primrec.unpair
  let check : ℕ → Bool := fun v =>
    decide ((Nat.unpair (Nat.unpair v).1).2 ≤ (Nat.unpair (Nat.unpair v).2).1) &&
      E (Nat.unpair (Nat.unpair v).1).1 (Nat.unpair (Nat.unpair v).2).1
        (Nat.unpair (Nat.unpair v).2).2
  have hc : Computable check := Primrec.and.to_comp.comp
    (Primrec.nat_le.comp (s.comp f) (f.comp s)).decide.to_comp
    (hE.comp ((f.comp f).pair ((f.comp s).pair (s.comp s))).to_comp)
  have hb : Pi zeroOracle 0 (fun v => check v = true) := recursive_bool hc
  apply (forall_form (exists_form hb)).congr
  intro r
  simp only [check, Nat.unpair_pair, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h b
    obtain ⟨z, hz, he⟩ := h b
    exact ⟨(Nat.unpair z).1, hz, (Nat.unpair z).2, he⟩
  · intro h b
    obtain ⟨n, hn, t, ht⟩ := h b
    exact ⟨Nat.pair n t, by simpa using And.intro hn ht⟩

/-- Cofinality can be decided by the actual second halting jump. -/
theorem cofinal_recursive : RecursivePred (zeroJump 2) (Cofinal E) :=
  form_recursive (cofinal_pi_two hE)

/-- Emptiness of a uniformly enumerable reservoir is uniformly Π₁. -/
theorem empty_pi_one : Pi zeroOracle 1 (Empty E) := by
  let f := Primrec.fst.comp Primrec.unpair
  let s := Primrec.snd.comp Primrec.unpair
  have hc : Computable (fun v : ℕ =>
      E (Nat.unpair v).1 (Nat.unpair (Nat.unpair v).2).1
        (Nat.unpair (Nat.unpair v).2).2) :=
    hE.comp (f.pair ((f.comp s).pair (s.comp s))).to_comp
  have hb : Sigma zeroOracle 0 (fun v =>
      ¬ E (Nat.unpair v).1 (Nat.unpair (Nat.unpair v).2).1
        (Nat.unpair (Nat.unpair v).2).2 = true) :=
    recursive_not (recursive_bool hc)
  apply (forall_form hb).congr
  intro r
  simp only [Nat.unpair_pair, Bool.not_eq_true]
  constructor
  · intro h n t
    simpa using h (Nat.pair n t)
  · intro h z
    exact h _ _

/-- Empty-set decisions need only the first jump. -/
theorem empty_recursive : RecursivePred (zeroJump 1) (Empty E) :=
  form_recursive (empty_pi_one hE)

theorem empty_recursive_two : RecursivePred (zeroJump 2) (Empty E) :=
  recursive_transfer (empty_recursive hE) (zeroJump_mono (by decide))

omit hE in
/-- Cofinality is preserved after removing any finite initial segment. -/
theorem Cofinal.tail {r : ℕ} (h : Cofinal E r) (b : ℕ) :
    ∀ k, ∃ n, k ≤ n ∧ b ≤ n ∧ Member E r n := by
  intro k
  obtain ⟨n, hn, hm⟩ := h (max k b)
  exact ⟨n, (Nat.le_max_left _ _).trans hn, (Nat.le_max_right _ _).trans hn, hm⟩

end Klr.Computability.CeCofinality
