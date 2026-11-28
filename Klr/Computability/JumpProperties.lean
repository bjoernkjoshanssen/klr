module

public import Klr.Computability.OracleJump

/-!
# Basic properties of the oracle jump

Oracle reduction is preserved by the jump, each oracle reduces to its jump,
and the finite jump iterates are monotone. `zeroJump` names the iterates above
the computable empty oracle, including the fourth and fifth jumps used in the
planned effective separation theorem.

The initial monotonicity proofs are adapted from `bjoernkjoshanssen/tt-auto`,
commit `3190d8d1a78e709297423d1343f68395127be5de`,
`OAI/Computability/DegreeRigidity/Computability/JumpProperties.lean`
(Apache-2.0). Degree-quotient infrastructure has been removed.
-/

@[expose] public section

namespace Klr.Computability.OracleJump

open Encodable OracleSimulation ArithmeticHierarchy

theorem recursive_transfer {Y Z : Oracle} {P : ℕ → Prop}
    (h : RecursivePred Y P) (hYZ : Reduces Y Z) : RecursivePred Z P :=
  RecursiveIn.iff_nat.mp (TuringReducible.trans (RecursiveIn.iff_nat.mpr h) hYZ)

theorem recursive_lift {Y : Oracle} {P : ℕ → Prop} (h : RecursivePred Y P) :
    RecursivePred (jump Y) P := by
  have hh := exists_recursive_jump (recursive_comp h (Primrec.fst.comp Primrec.unpair))
  exact Form.congr (n := 0) (s := true) hh (fun x => by simp)

theorem reduces_jump (Y : Oracle) : Reduces Y (jump Y) := by
  have h : RecursivePred Y (fun x => Y x = true) := by
    classical
    have hq : Nat.RecursiveIn {oracleFunction Y} (oracleFunction Y) :=
      .oracle _ (Set.mem_singleton _)
    exact hq.of_eq (fun x => by cases hy : Y x <;> simp [oracleFunction, bit, hy])
  apply RecursiveIn.iff_nat.mpr
  exact (recursive_lift h).of_eq (fun x => by cases hy : Y x <;> simp [oracleFunction, bit, hy])

theorem halts_sigma (Y : Oracle) :
    Sigma Y 1 (fun v => Halts Y (Nat.unpair v).1 (Nat.unpair v).2) := by
  classical
  let f := Primrec.fst.comp Primrec.unpair
  let s := Primrec.snd.comp Primrec.unpair
  have ht := total_comp (run_uniform_recursive Y) (total_primrec
    (Primrec₂.natPair.comp (f.comp f) (Primrec₂.natPair.comp (s.comp f) s)))
  have hcheck : Primrec (fun v : ℕ => bit ((decode (α := Option ℕ) v).getD none).isSome) :=
    bit_primrec.comp (Primrec.option_isSome.comp
      (Primrec.option_getD.comp Primrec.decode (Primrec.const none)))
  have h : RecursivePred Y (fun v =>
      (OracleSimulation.run Y (machine (Nat.unpair (Nat.unpair v).1).1)
        (Nat.unpair (Nat.unpair v).1).2 (Nat.unpair v).2).isSome = true) := by
    exact (total_comp (total_primrec hcheck) ht).of_eq (fun v => by
      simp only [Nat.unpair_pair, encodek, Option.getD_some, bit]
      congr 1
      split <;> rfl)
  apply (exists_form (n := 0) h).congr
  intro v
  simp only [Nat.unpair_pair, Halts]
  apply exists_congr
  intro z
  cases OracleSimulation.run Y (machine (Nat.unpair v).1) (Nat.unpair v).2 z <;> simp

theorem jump_mono {Y Z : Oracle} (hYZ : Reduces Y Z) : Reduces (jump Y) (jump Z) := by
  obtain ⟨Q, hQ, he⟩ := halts_sigma Y
  have h := exists_recursive_jump (recursive_transfer hQ hYZ)
  have h' : RecursivePred (jump Z) (fun v => Halts Y (Nat.unpair v).1 (Nat.unpair v).2) :=
    Form.congr (n := 0) (s := true) h (fun v => (he v).symm)
  apply RecursiveIn.iff_nat.mpr
  exact h'.of_eq (fun v => by
    classical
    by_cases h : Halts Y (Nat.unpair v).1 (Nat.unpair v).2 <;> simp [oracleFunction, bit, jump, h])

theorem iterate_mono {Y Z : Oracle} (hYZ : Reduces Y Z) (n : ℕ) :
    Reduces (iterate Y n) (iterate Z n) := by
  induction n with
  | zero => exact hYZ
  | succ n ih => exact jump_mono ih

/-- The relative halting jump is not computable from its oracle. The proof
constructs a relative partial program that halts exactly when its proposed
halting decision says that it does not, and applies `partial_table` diagonally. -/
theorem jump_not_reduces (A : Oracle) : ¬ Reduces (jump A) A := by
  classical
  intro h
  have hd0 := recursive_comp (form_recursive (halts_sigma A))
    (Primrec₂.natPair.comp Primrec.id Primrec.id)
  have hd : RecursivePred A (fun n => Halts A n n) := by
    simpa only [Nat.unpair_pair, id_eq] using recursive_transfer hd0 h
  have hm := recursive_comp hd (Primrec.fst.comp Primrec.unpair)
  have hs := Nat.RecursiveIn.rfind hm
  obtain ⟨e, he⟩ := partial_table hs
  have hee : Halts A e e ↔ ¬ Halts A e e := by
    refine (he e).trans ?_
    erw [Nat.rfind_dom]
    simp
  by_cases hh : Halts A e e
  · exact (hee.mp hh) hh
  · exact hh (hee.mpr hh)

/-- An oracle reduces to every one of its finite jump iterates. -/
theorem reduces_iterate (A : Oracle) (n : ℕ) : Reduces A (iterate A n) := by
  induction n with
  | zero => exact reduces_refl A
  | succ n ih => exact reduces_trans ih (reduces_jump (iterate A n))

/-- Iterating first `m` and then `n` times is the `(m+n)`-fold jump. -/
theorem iterate_add (A : Oracle) (m n : ℕ) :
    iterate A (m + n) = iterate (iterate A m) n := by
  induction n with
  | zero => simp
  | succ n ih => exact congrArg jump ih

/-- The number of iterations is monotone in Turing reducibility. -/
theorem iterate_le_iterate (A : Oracle) {m n : ℕ} (h : m ≤ n) :
    Reduces (iterate A m) (iterate A n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [iterate_add]
  exact reduces_iterate (iterate A m) k

/-- The usual finite jump hierarchy above the computable empty oracle. -/
noncomputable def zeroJump (n : ℕ) : Oracle := iterate zeroOracle n

@[simp] theorem zeroJump_zero : zeroJump 0 = zeroOracle := rfl

@[simp] theorem zeroJump_succ (n : ℕ) : zeroJump (n + 1) = jump (zeroJump n) := rfl

theorem zeroJump_mono {m n : ℕ} (h : m ≤ n) : Reduces (zeroJump m) (zeroJump n) :=
  iterate_le_iterate zeroOracle h

/-- Successive finite jumps are strictly increasing in Turing degree. -/
theorem zeroJump_succ_not_reduces (n : ℕ) :
    ¬ Reduces (zeroJump (n + 1)) (zeroJump n) :=
  jump_not_reduces (zeroJump n)

/-- A strictly later finite jump cannot reduce to an earlier one. -/
theorem zeroJump_not_reduces_of_lt {m n : ℕ} (h : m < n) :
    ¬ Reduces (zeroJump n) (zeroJump m) := by
  intro hnm
  exact zeroJump_succ_not_reduces m
    (reduces_trans (zeroJump_mono (Nat.succ_le_of_lt h)) hnm)

/-- The oracle inclusion used by the effective-partition construction. -/
theorem firstJump_reduces_fourth : Reduces (zeroJump 1) (zeroJump 4) :=
  zeroJump_mono (by decide)

/-- The final witness-selection step passes from the fourth to the fifth jump. -/
theorem fourthJump_reduces_fifth : Reduces (zeroJump 4) (zeroJump 5) :=
  zeroJump_mono (by decide)

/-- A Σ or Π predicate at level `n` above the empty oracle is decidable in
`zeroJump n`. -/
theorem form_recursive_zero {n s P} (h : Form zeroOracle n s P) :
    RecursivePred (zeroJump n) P :=
  form_recursive h

/-- The arithmetical hierarchy upper bound, as a Turing reduction of sets. -/
theorem form_reduces {A n s P} (h : Form A n s P) :
    Reduces (predicateOracle P) (iterate A n) :=
  (recursivePred_iff_reduces _ _).mp (form_recursive h)

end Klr.Computability.OracleJump
