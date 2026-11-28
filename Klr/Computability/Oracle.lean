module

public import Mathlib.Computability.PartrecCode
public import Mathlib.Computability.TuringDegree
public import Mathlib.Computability.Primrec.List
public import Mathlib.Tactic

/-!
# Boolean oracles and relative computation

The oracle model is Mathlib's `RecursiveIn`, specialized to the total
characteristic function of a set of natural numbers. No oracle computation
or reducibility principle is added as an axiom.

The elementary total-function helpers are adapted from
`bjoernkjoshanssen/tt-auto`, commit
`3190d8d1a78e709297423d1343f68395127be5de`,
`OAI/Computability/DegreeRigidity/Effective/UniformOracle.lean` (Apache-2.0).
They are extracted here without the degree-rigidity development.
-/

@[expose] public section

namespace Klr.Computability

/-- A set of natural numbers, presented by its characteristic bits. -/
abbrev Oracle := ℕ → Bool

/-- Convert an oracle bit to the natural-number output used by `RecursiveIn`. -/
def bit (b : Bool) : ℕ := if b then 1 else 0

@[simp] theorem bit_false : bit false = 0 := rfl
@[simp] theorem bit_true : bit true = 1 := rfl

theorem bit_primrec : Primrec bit := by
  apply (Primrec.cond Primrec.id (Primrec.const 1) (Primrec.const 0)).of_eq
  intro b
  cases b <;> rfl

/-- The total natural-valued characteristic function exposed to oracle programs. -/
def oracleFunction (A : Oracle) : ℕ →. ℕ := fun n => Part.some (bit (A n))

/-- Turing reducibility, using Mathlib's actual relative recursive functions. -/
def Reduces (A B : Oracle) : Prop :=
  TuringReducible (oracleFunction A) (oracleFunction B)

theorem reduces_refl (A : Oracle) : Reduces A A := TuringReducible.refl _

theorem reduces_trans {A B C : Oracle} (hAB : Reduces A B) (hBC : Reduces B C) :
    Reduces A C := TuringReducible.trans hAB hBC

theorem reduces_iff_recursiveIn (A B : Oracle) :
    Reduces A B ↔ Nat.RecursiveIn {oracleFunction B} (oracleFunction A) :=
  RecursiveIn.iff_nat

theorem oracleFunction_injective : Function.Injective oracleFunction := by
  intro A B h
  funext n
  have hn := congrFun h n
  cases hA : A n <;> cases hB : B n <;> simp_all [oracleFunction, bit]

section Total

variable {O : Set (ℕ →. ℕ)}

/-- Composition of total functions recursive in the same oracle set. -/
theorem total_comp {f g : ℕ → ℕ}
    (hf : Nat.RecursiveIn O (fun n => Part.some (f n)))
    (hg : Nat.RecursiveIn O (fun n => Part.some (g n))) :
    Nat.RecursiveIn O (fun n => Part.some (f (g n))) := by
  simpa using Nat.RecursiveIn.comp hf hg

/-- Pairing of total functions recursive in the same oracle set. -/
theorem total_pair {f g : ℕ → ℕ}
    (hf : Nat.RecursiveIn O (fun n => Part.some (f n)))
    (hg : Nat.RecursiveIn O (fun n => Part.some (g n))) :
    Nat.RecursiveIn O (fun n => Part.some (Nat.pair (f n) (g n))) := by
  simpa [Seq.seq] using Nat.RecursiveIn.pair hf hg

/-- Primitive recursive functions can be used with any oracle set. -/
theorem total_primrec {f : ℕ → ℕ} (hf : Primrec f) :
    Nat.RecursiveIn O (fun n => Part.some (f n)) :=
  RecursiveIn.iff_nat.mp hf.computableIn

/-- Ordinary computable functions can be used with any oracle set. -/
theorem total_computable {f : ℕ → ℕ} (hf : Computable f) :
    Nat.RecursiveIn O (fun n => Part.some (f n)) :=
  RecursiveIn.iff_nat.mp hf.computableIn

end Total

/-- The empty oracle, used as the base of the finite jump hierarchy. -/
def zeroOracle : Oracle := fun _ => false

theorem zeroOracle_reduces (A : Oracle) : Reduces zeroOracle A := by
  apply (reduces_iff_recursiveIn _ _).mpr
  change Nat.RecursiveIn {oracleFunction A} (fun _ => Part.some 0)
  exact total_primrec (Primrec.const 0)

/-- Computability relative to the empty oracle is ordinary computability. -/
theorem recursiveIn_zeroOracle_iff {f : ℕ →. ℕ} :
    RecursiveIn {oracleFunction zeroOracle} f ↔ Partrec f := by
  constructor
  · intro h
    change RecursiveIn {fun _ : ℕ => Part.some 0} f at h
    exact h.partrec_of_const
  · exact Partrec.recursiveIn

end Klr.Computability
