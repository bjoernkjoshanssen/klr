module

public import Klr.Computability.ArithmeticHierarchy
public import Klr.Computability.RelativeSearch
public import Klr.Computability.OracleJump

/-!
# Selecting witnesses to relative Σ₁ relations

If a uniformly Σ₁ relation relative to `A` has a witness for every input, an
`A`-computable function can select a witness. Search is performed over a pair
consisting of the desired witness and a certificate for the existential
definition. Thus a diverging or unsuccessful candidate never blocks the search.

The conclusion deliberately does not say that the selected semantic witness is
least. Least-witness search is used only for a predicate decidable in `A`.

The decidable-predicate minimization proof is adapted from
`bjoernkjoshanssen/tt-auto`, commit
`3190d8d1a78e709297423d1343f68395127be5de`,
`OAI/Computability/DegreeRigidity/Effective/EffectiveWitness.lean` (Apache-2.0).
The total Σ₁ selector below uses no jump and no absence-of-witness decision.
More generally, a total Σₙ₊₁ relation has a selector in the `n`-fold jump.
-/

@[expose] public section

namespace Klr.Computability.ArithmeticSelection

open ArithmeticHierarchy

/-- Least witnesses to a decidable relation; computability is proved separately. -/
noncomputable def least (P : ℕ → Prop) (htotal : ∀ n, ∃ a, P (Nat.pair n a))
    (n : ℕ) : ℕ := by
  classical
  exact Nat.find (htotal n)

theorem least_spec (P : ℕ → Prop) (htotal : ∀ n, ∃ a, P (Nat.pair n a))
    (n : ℕ) : P (Nat.pair n (least P htotal n)) := by
  classical
  exact Nat.find_spec (htotal n)

/-- Minimization of an `A`-decidable total relation uses the same oracle. -/
theorem least_recursive {A : Oracle} {P : ℕ → Prop} (hP : RecursivePred A P)
    (htotal : ∀ n, ∃ a, P (Nat.pair n a)) :
    Nat.RecursiveIn {oracleFunction A} (fun n => Part.some (least P htotal n)) := by
  classical
  apply (Nat.RecursiveIn.rfind (recursive_not hP)).of_eq_tot
  intro n
  apply Nat.mem_rfind.mpr
  constructor
  · simp [least_spec P htotal n]
  · intro a ha
    have hn := Nat.find_min (htotal n) (show a < Nat.find (htotal n) from ha)
    simp [hn]

/-- Every total relative Σ₁ relation has a selector computable in the same
oracle. The search pairs each proposed output with its existential certificate. -/
theorem exists_selector_of_sigma_one {A : Oracle} {P : ℕ → Prop}
    (hP : Sigma A 1 P) (htotal : ∀ n, ∃ a, P (Nat.pair n a)) :
    ∃ f : ℕ → ℕ,
      Nat.RecursiveIn {oracleFunction A} (fun n => Part.some (f n)) ∧
      ∀ n, P (Nat.pair n (f n)) := by
  obtain ⟨Q, hQ, hPQ⟩ := hP
  let R : ℕ → Prop := fun v =>
    Q (Nat.pair (Nat.pair (Nat.unpair v).1 (Nat.unpair (Nat.unpair v).2).1)
      (Nat.unpair (Nat.unpair v).2).2)
  let fst := Primrec.fst.comp Primrec.unpair
  let snd := Primrec.snd.comp Primrec.unpair
  have hR : RecursivePred A R := recursive_comp hQ
    (Primrec₂.natPair.comp (Primrec₂.natPair.comp fst (fst.comp snd)) (snd.comp snd))
  have hRtotal : ∀ n, ∃ code, R (Nat.pair n code) := by
    intro n
    obtain ⟨a, ha⟩ := htotal n
    obtain ⟨certificate, hc⟩ := (hPQ (Nat.pair n a)).mp ha
    exact ⟨Nat.pair a certificate, by simpa [R] using hc⟩
  let f : ℕ → ℕ := fun n => (Nat.unpair (least R hRtotal n)).1
  have hf := total_comp (total_primrec (Primrec.fst.comp Primrec.unpair))
    (least_recursive hR hRtotal)
  refine ⟨f, hf, fun n => ?_⟩
  apply (hPQ (Nat.pair n (f n))).mpr
  refine ⟨(Nat.unpair (least R hRtotal n)).2, ?_⟩
  simpa only [R, Nat.unpair_pair] using least_spec R hRtotal n

/-- The relative Σ₁ selection theorem with Mathlib's `ComputableIn` interface. -/
theorem exists_computableIn_selector_of_sigma_one {A : Oracle} {P : ℕ → Prop}
    (hP : Sigma A 1 P) (htotal : ∀ n, ∃ a, P (Nat.pair n a)) :
    ∃ f : ℕ → ℕ, ComputableIn {oracleFunction A} f ∧
      ∀ n, P (Nat.pair n (f n)) := by
  obtain ⟨f, hf, hspec⟩ := exists_selector_of_sigma_one hP htotal
  exact ⟨f, RecursiveIn.iff_nat.mpr hf, hspec⟩

/-- A total Σₙ₊₁ relation has a selector computable in the `n`-fold jump.
The outer existential quantifier is searched, while the matrix is decided
using the hierarchy upper bound. -/
theorem exists_selector_of_sigma_succ {A : Oracle} {n : ℕ} {P : ℕ → Prop}
    (hP : Sigma A (n + 1) P) (htotal : ∀ x, ∃ a, P (Nat.pair x a)) :
    ∃ f : ℕ → ℕ,
      Nat.RecursiveIn {oracleFunction (OracleJump.iterate A n)}
        (fun x => Part.some (f x)) ∧
      ∀ x, P (Nat.pair x (f x)) := by
  obtain ⟨Q, hQ, hPQ⟩ := hP
  have hrel : Sigma (OracleJump.iterate A n) 1 P :=
    ⟨Q, OracleJump.form_recursive hQ, hPQ⟩
  exact exists_selector_of_sigma_one hrel htotal

/-- Higher-level relative selection in Mathlib's total-computability notation. -/
theorem exists_computableIn_selector_of_sigma_succ {A : Oracle} {n : ℕ} {P : ℕ → Prop}
    (hP : Sigma A (n + 1) P) (htotal : ∀ x, ∃ a, P (Nat.pair x a)) :
    ∃ f : ℕ → ℕ, ComputableIn {oracleFunction (OracleJump.iterate A n)} f ∧
      ∀ x, P (Nat.pair x (f x)) := by
  obtain ⟨f, hf, hspec⟩ := exists_selector_of_sigma_succ hP htotal
  exact ⟨f, RecursiveIn.iff_nat.mpr hf, hspec⟩

/-- A least semantic witness can be selected after deciding the whole predicate
in the jump supplied by its arithmetic level. This differs from the sharper
non-least Σₙ₊₁ selector above. -/
theorem least_recursive_of_form {A : Oracle} {n : ℕ} {polarity : Bool} {P : ℕ → Prop}
    (hP : Form A n polarity P) (htotal : ∀ x, ∃ a, P (Nat.pair x a)) :
    Nat.RecursiveIn {oracleFunction (OracleJump.iterate A n)}
      (fun x => Part.some (least P htotal x)) :=
  least_recursive (OracleJump.form_recursive hP) htotal

end Klr.Computability.ArithmeticSelection
