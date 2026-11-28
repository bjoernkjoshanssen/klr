module

public import Klr.Computability.Oracle

/-!
# Iterating oracle-computable stage operations

Primitive recursion and iteration preserve the oracle. The partial-transition
version allows a stage search to halt only on valid histories: an invariant
proves that the particular run from the initial history is total.
-/

@[expose] public section

namespace Klr.Computability

variable {O : Set (ℕ →. ℕ)}

/-- Parameterized primitive recursion on total oracle-computable functions.
The step input is coded as `(parameter, (stage, previous value))`. -/
theorem total_prec {f : ℕ → ℕ} {g : ℕ → ℕ → ℕ → ℕ}
    (hf : Nat.RecursiveIn O (fun a => Part.some (f a)))
    (hg : Nat.RecursiveIn O (fun p => Part.some
      (g (Nat.unpair p).1 (Nat.unpair (Nat.unpair p).2).1
        (Nat.unpair (Nat.unpair p).2).2))) :
    Nat.RecursiveIn O (fun p => Part.some
      (Nat.rec (f (Nat.unpair p).1)
        (fun n v => g (Nat.unpair p).1 n v) (Nat.unpair p).2)) := by
  apply (Nat.RecursiveIn.prec hf hg).of_eq
  intro p
  dsimp only
  simp only [Nat.unpair_pair, Part.bind_eq_bind]
  generalize (Nat.unpair p).1 = a
  generalize (Nat.unpair p).2 = n
  induction n with
  | zero => rfl
  | succ n ih => simp [ih]

/-- Iterating one total stage function introduces no new oracle. -/
theorem total_iterate {f : ℕ → ℕ}
    (hf : Nat.RecursiveIn O (fun a => Part.some (f a))) (a : ℕ) :
    Nat.RecursiveIn O (fun n => Part.some (f^[n] a)) := by
  have hs := total_comp hf (total_primrec
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
  have hr := total_prec (g := fun _ _ v => f v)
    (total_primrec (O := O) (Primrec.const a)) hs
  have h := total_comp hr
    (total_pair (total_primrec (Primrec.const 0)) (total_primrec Primrec.id))
  apply h.of_eq
  intro n
  simp only [Nat.unpair_pair, id_eq]
  congr 1
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Function.iterate_succ_apply'] using congrArg f ih

/-- Iterate a partial stage transition, stopping whenever that transition diverges. -/
def partialIterate (step : ℕ →. ℕ) (initial : ℕ) : ℕ →. ℕ
  | 0 => Part.some initial
  | n + 1 => partialIterate step initial n >>= step

theorem partialIterate_recursiveIn {step : ℕ →. ℕ}
    (hstep : Nat.RecursiveIn O step) (initial : ℕ) :
    Nat.RecursiveIn O (partialIterate step initial) := by
  have hs : Nat.RecursiveIn O (fun p => step (Nat.unpair (Nat.unpair p).2).2) := by
    apply (Nat.RecursiveIn.comp hstep (total_primrec
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))).of_eq
    intro p
    exact Part.bind_some _ _
  have hr := Nat.RecursiveIn.prec (total_primrec (O := O) (Primrec.const initial)) hs
  have h := Nat.RecursiveIn.comp hr
    (total_pair (total_primrec (Primrec.const 0)) (total_primrec Primrec.id))
  apply h.of_eq
  intro n
  change (Part.some (Nat.pair 0 n)).bind _ = _
  rw [Part.bind_some]
  simp only [Nat.unpair_pair]
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun q : Part ℕ => q >>= step) ih

/-- An invariant can establish totality of a particular run without assuming
that the transition halts on every natural-number state. -/
theorem partialIterate_invariant {step : ℕ →. ℕ} {initial : ℕ}
    {Valid : ℕ → Prop} (hinitial : Valid initial)
    (hnext : ∀ s, Valid s → ∃ t, t ∈ step s ∧ Valid t) :
    ∀ n, ∃ s, s ∈ partialIterate step initial n ∧ Valid s := by
  intro n
  induction n with
  | zero => exact ⟨initial, Part.mem_some _, hinitial⟩
  | succ n ih =>
    obtain ⟨s, hs, hVs⟩ := ih
    obtain ⟨t, ht, hVt⟩ := hnext s hVs
    exact ⟨t, Part.mem_bind_iff.mpr ⟨s, hs, ht⟩, hVt⟩

/-- A partial oracle-computable transition with a preserved invariant yields
a total run computable in the same oracle. -/
theorem exists_computable_run {step : ℕ →. ℕ}
    (hstep : Nat.RecursiveIn O step) {initial : ℕ} {Valid : ℕ → Prop}
    (hinitial : Valid initial)
    (hnext : ∀ s, Valid s → ∃ t, t ∈ step s ∧ Valid t) :
    ∃ run : ℕ → ℕ,
      Nat.RecursiveIn O (fun n => Part.some (run n)) ∧ run 0 = initial ∧
      (∀ n, Valid (run n)) ∧ ∀ n, run (n + 1) ∈ step (run n) := by
  classical
  choose run hrun hvalid using partialIterate_invariant hinitial hnext
  refine ⟨run, (partialIterate_recursiveIn hstep initial).of_eq_tot hrun, ?_, hvalid, ?_⟩
  · exact Part.mem_some_iff.mp (hrun 0)
  · intro n
    obtain ⟨s, hs, ht⟩ := Part.mem_bind_iff.mp (hrun (n + 1))
    have he : s = run n := Part.mem_unique hs (hrun n)
    simpa only [he] using ht

end Klr.Computability
