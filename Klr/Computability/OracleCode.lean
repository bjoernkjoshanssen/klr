module

public import Klr.Computability.Oracle
public import Mathlib.Computability.PartrecCode

/-!
# Programs for relative partial recursive functions

`OracleCode` is syntax for the constructors of Mathlib's `Nat.RecursiveIn`.
Its evaluator accepts an arbitrary partial numerical oracle. Soundness and
completeness connect the syntax directly to Mathlib's existing definition.
The parametric evaluator remains partial recursive whenever its oracle is
partial recursive in the ordinary input parameters.

The evaluator and proofs are adapted from `bjoernkjoshanssen/tt-auto`, commit
`3190d8d1a78e709297423d1343f68395127be5de`, files `Computability/OracleCode.lean`,
`SetModels/ParametricEval.lean`, and `Effective/PartialComputability.lean` under
`OAI/Computability/DegreeRigidity`. That project is distributed under Apache 2.0.
The degree-rigidity dependencies and unrelated countability statements have
been removed; the mathematical evaluator and completeness proofs are retained.
-/

@[expose] public section

namespace Klr.Computability

inductive OracleCode where
  | zero | succ | left | right | query
  | pair : OracleCode → OracleCode → OracleCode
  | comp : OracleCode → OracleCode → OracleCode
  | prec : OracleCode → OracleCode → OracleCode
  | find : OracleCode → OracleCode


namespace OracleCode

def eval (g : ℕ →. ℕ) : OracleCode → ℕ →. ℕ
  | .zero => fun _ => 0
  | .succ => Nat.succ
  | .left => fun n => (Nat.unpair n).1
  | .right => fun n => (Nat.unpair n).2
  | .query => g
  | .pair c d => fun n => Nat.pair <$> eval g c n <*> eval g d n
  | .comp c d => fun n => eval g d n >>= eval g c
  | .prec c d => fun p =>
      let (a, n) := Nat.unpair p
      n.rec (eval g c a) fun y ih => do
        let i ← ih
        eval g d (Nat.pair a (Nat.pair y i))
  | .find c => fun a =>
      Nat.rfind fun n => (fun m => m = 0) <$> eval g c (Nat.pair a n)

theorem eval_recursiveIn (g : ℕ →. ℕ) (c : OracleCode) :
    Nat.RecursiveIn {g} (eval g c) := by
  induction c with
  | zero => exact .zero
  | succ => exact .succ
  | left => exact .left
  | right => exact .right
  | query => exact .oracle g (Set.mem_singleton g)
  | pair c d hc hd => exact .pair hc hd
  | comp c d hc hd => exact .comp hc hd
  | prec c d hc hd => exact .prec hc hd
  | find c hc => exact .rfind hc

theorem exists_code {g f : ℕ →. ℕ} (hf : Nat.RecursiveIn {g} f) :
    ∃ c : OracleCode, eval g c = f := by
  induction hf with
  | zero => exact ⟨.zero, rfl⟩
  | succ => exact ⟨.succ, rfl⟩
  | left => exact ⟨.left, rfl⟩
  | right => exact ⟨.right, rfl⟩
  | oracle f hf =>
      have hfg : f = g := Set.mem_singleton_iff.mp hf
      subst f
      exact ⟨.query, rfl⟩
  | pair _ _ hc hd =>
      obtain ⟨c, rfl⟩ := hc
      obtain ⟨d, rfl⟩ := hd
      exact ⟨.pair c d, rfl⟩
  | comp _ _ hc hd =>
      obtain ⟨c, rfl⟩ := hc
      obtain ⟨d, rfl⟩ := hd
      exact ⟨.comp c d, rfl⟩
  | prec _ _ hc hd =>
      obtain ⟨c, rfl⟩ := hc
      obtain ⟨d, rfl⟩ := hd
      exact ⟨.prec c d, rfl⟩
  | rfind _ hc =>
      obtain ⟨c, rfl⟩ := hc
      exact ⟨.find c, rfl⟩

theorem turingReducible_iff_exists_code (f g : ℕ →. ℕ) :
    TuringReducible f g ↔ ∃ c : OracleCode, eval g c = f := by
  change RecursiveIn {g} f ↔ _
  rw [RecursiveIn.iff_nat]
  exact ⟨exists_code, fun ⟨c, hc⟩ => hc ▸ eval_recursiveIn g c⟩


open Computable

theorem eval_partrec {α : Type*} [Primcodable α] {g : α → ℕ →. ℕ}
    (hg : Partrec₂ g) (c : OracleCode) : Partrec₂ (fun a n => eval (g a) c n) := by
  induction c with
  | zero => exact Computable.const 0
  | succ => exact Computable.succ.comp snd
  | left => exact (fst.comp Computable.unpair).comp snd
  | right => exact (snd.comp Computable.unpair).comp snd
  | query => exact hg
  | pair c d hc hd =>
    change Partrec (fun z : α × ℕ =>
      (eval (g z.1) c z.2).bind (fun a => (eval (g z.1) d z.2).map (Nat.pair a)))
    apply Partrec.bind hc
    apply Partrec.map (hd.comp (fst.comp fst) (snd.comp fst))
    exact Primrec₂.natPair.to_comp.comp (snd.comp fst) snd
  | comp c d hc hd =>
    exact hd.bind (hc.comp (fst.comp fst) snd)
  | prec c d hc hd =>
    exact Partrec.nat_rec ((snd.comp Computable.unpair).comp snd)
      (hc.comp fst ((fst.comp Computable.unpair).comp snd))
      (hd.comp (fst.comp fst)
        (Primrec₂.natPair.to_comp.comp ((fst.comp Computable.unpair).comp (snd.comp fst))
          (Primrec₂.natPair.to_comp.comp (fst.comp snd) (snd.comp snd)))).to₂
  | find c hc =>
    exact Partrec.rfind ((hc.comp (fst.comp fst)
      (Primrec₂.natPair.to_comp.comp (snd.comp fst) snd)).map
        ((Primrec.beq.comp Primrec.snd (Primrec.const 0)).to_comp))


end OracleCode

/-- Compile a partial recursive function on a coded input type into an ordinary program. -/
theorem partrec_code {α : Type*} [Primcodable α] {f : α →. ℕ} (hf : Partrec f) :
    ∃ c : Nat.Partrec.Code, ∀ a, c.eval (Encodable.encode a) = f a := by
  obtain ⟨c,hc⟩ := Nat.Partrec.Code.exists_code.mp hf
  refine ⟨c, fun a => ?_⟩
  simp [hc, Encodable.encodek, Part.map_id']


end Klr.Computability
