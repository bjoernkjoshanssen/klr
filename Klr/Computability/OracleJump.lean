module

public import Klr.Computability.ArithmeticHierarchy
public import Klr.Computability.OracleSimulation

/-!
# Oracle halting, jumps, and the hierarchy upper bound

`jump A` codes the halting questions for finite-oracle simulations. Every partial
function recursive in `A` has such a simulation, proved in `partial_table`.
The resulting completeness theorem supplies the upper-bound direction of Post's
theorem: a level-`n` relative arithmetic predicate is decidable in `iterate A n`.

These proofs are adapted from `bjoernkjoshanssen/tt-auto`, commit
`3190d8d1a78e709297423d1343f68395127be5de`,
`OAI/Computability/DegreeRigidity/Computability/OracleJump.lean`
(Apache-2.0). The jump is defined from actual bounded program evaluation; no
halting or hierarchy principle is assumed as an axiom.
-/

@[expose] public section

namespace Klr.Computability.OracleJump

open Encodable OracleSimulation ArithmeticHierarchy

def Halts (Y : Oracle) (e n : ℕ) : Prop := ∃ z a, a ∈ OracleSimulation.run Y (machine e) n z

noncomputable def jump (Y : Oracle) : Oracle := by
  classical
  exact fun v => decide (Halts Y (Nat.unpair v).1 (Nat.unpair v).2)

theorem partial_table {Y : Oracle} {f : ℕ →. ℕ}
    (hf : Nat.RecursiveIn {oracleFunction Y} f) :
    ∃ e, ∀ n, Halts Y e n ↔ (f n).Dom := by
  obtain ⟨c, hc⟩ := OracleCode.exists_code hf
  have hh : Partrec₂ (fun L : List ℕ => fun n => OracleCode.eval (OracleSimulation.lookup L) c n) :=
    OracleCode.eval_partrec OracleSimulation.lookup_partrec c
  obtain ⟨d, hd⟩ := partrec_code hh
  have hd' : ∀ L n, d.eval (Nat.pair (encode L) n) =
      OracleCode.eval (OracleSimulation.lookup L) c n :=
    fun L n => hd (L, n)
  have ha (n : ℕ) : Approximates (f n)
      (fun m => d.eval (Nat.pair (encode (oraclePrefix (fun k => bit (Y k)) m)) n)) := by
    simp only [hd', ← hc]
    exact OracleCode.eval_approximates (prefix_approximates (fun k => bit (Y k))) c n
  refine ⟨encode d, fun n => ?_⟩
  constructor
  · rintro ⟨z, a, ha'⟩
    simp only [machine_encode] at ha'
    exact ((ha n).1 (Nat.unpair z).1 a (Nat.Partrec.Code.evaln_sound ha')).1
  · intro hf'
    obtain ⟨m, hm⟩ := (ha n).2 ((f n).get hf') ⟨hf', rfl⟩
    obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp (hm m le_rfl)
    exact ⟨Nat.pair m t, (f n).get hf', by simpa [OracleSimulation.run, trial] using ht⟩

theorem domain_recursive_jump {Y : Oracle} {f : ℕ →. ℕ}
    (hf : Nat.RecursiveIn {oracleFunction Y} f) :
    RecursivePred (jump Y) (fun n => (f n).Dom) := by
  classical
  obtain ⟨e, he⟩ := partial_table hf
  have hq : Nat.RecursiveIn {oracleFunction (jump Y)} (oracleFunction (jump Y)) :=
    .oracle _ (Set.mem_singleton _)
  have h := Nat.RecursiveIn.comp hq
    (total_primrec (Primrec₂.natPair.comp (Primrec.const e) Primrec.id))
  exact h.of_eq (fun n => by
    change (Part.some (Nat.pair e n)).bind
      (fun input => Part.some (if jump Y input then 1 else 0)) = _
    rw [Part.bind_some]
    simp [jump, he])

theorem exists_recursive_jump {Y : Oracle} {P : ℕ → Prop} (hP : RecursivePred Y P) :
    RecursivePred (jump Y) (fun x => ∃ a, P (Nat.pair x a)) := by
  classical
  have hN := recursive_not hP
  have hs := Nat.RecursiveIn.rfind hN
  have hd := domain_recursive_jump hs
  apply Form.congr (n := 0) (s := true) hd
  intro x
  erw [Nat.rfind_dom]
  simp

theorem forall_recursive_jump {Y : Oracle} {P : ℕ → Prop} (hP : RecursivePred Y P) :
    RecursivePred (jump Y) (fun x => ∀ a, P (Nat.pair x a)) := by
  have h := recursive_not (exists_recursive_jump (recursive_not hP))
  simpa only [not_exists, not_not] using h

/-- The finite iterates of the relative halting jump. -/
noncomputable def iterate (Y : Oracle) : ℕ → Oracle
  | 0 => Y
  | n + 1 => jump (iterate Y n)

@[simp] theorem iterate_zero (Y : Oracle) : iterate Y 0 = Y := rfl

@[simp] theorem iterate_succ (Y : Oracle) (n : ℕ) :
    iterate Y (n + 1) = jump (iterate Y n) := rfl

/-- The upper-bound direction of Post's theorem, for either Σ or Π levels. -/
theorem form_recursive {Y n s P} (h : Form Y n s P) : RecursivePred (iterate Y n) P := by
  induction n generalizing s P with
  | zero => exact h
  | succ n ih =>
    obtain ⟨Q, hQ, he⟩ := h
    have hr := ih hQ
    cases s with
    | false =>
      have hh := forall_recursive_jump hr
      have he' : (fun x => ∀ a, Q (Nat.pair x a)) = P := funext (fun x => propext (he x).symm)
      exact he' ▸ hh
    | true =>
      have hh := exists_recursive_jump hr
      have he' : (fun x => ∃ a, Q (Nat.pair x a)) = P := funext (fun x => propext (he x).symm)
      exact he' ▸ hh

end Klr.Computability.OracleJump
