module

public import Klr.Computability.OracleRecursion
public import Klr.Computability.JumpProperties

/-!
# Typed operations on relative computable functions

These helpers lift Mathlib's numerical oracle operations to `Primcodable`
types. Finite recursion and tabulation preserve the oracle.
-/

@[expose] public section

namespace Klr.Computability.RelativeComputable

open Encodable

variable {α β γ δ : Type*} [Primcodable α] [Primcodable β]
  [Primcodable γ] [Primcodable δ] {O : Set (ℕ →. ℕ)}

theorem of_eq {f g : α → β} (hf : ComputableIn O f) (h : ∀ a, f a = g a) :
    ComputableIn O g :=
  (funext h : f = g) ▸ hf

theorem of_computable {f : α → β} (hf : Computable f) : ComputableIn O f :=
  hf.computableIn

theorem comp {f : β → γ} {g : α → β}
    (hf : ComputableIn O f) (hg : ComputableIn O g) :
    ComputableIn O (fun a => f (g a)) := by
  change Nat.RecursiveIn O _ at hf hg ⊢
  apply (Nat.RecursiveIn.comp hf hg).of_eq
  intro n
  cases decode (α := α) n <;> simp

theorem pair {f : α → β} {g : α → γ}
    (hf : ComputableIn O f) (hg : ComputableIn O g) :
    ComputableIn O (fun a => (f a, g a)) := by
  change Nat.RecursiveIn O _ at hf hg ⊢
  apply (Nat.RecursiveIn.pair hf hg).of_eq
  intro n
  cases decode (α := α) n <;> simp [Seq.seq, encode_prod_val]

theorem comp₂ {f : β → γ → δ} {g : α → β} {h : α → γ}
    (hf : ComputableIn₂ O f) (hg : ComputableIn O g) (hh : ComputableIn O h) :
    ComputableIn O (fun a => f (g a) (h a)) :=
  comp hf (pair hg hh)

theorem mono {O' : Set (ℕ →. ℕ)} {f : α → β}
    (hO : O ⊆ O') (hf : ComputableIn O f) : ComputableIn O' f :=
  RecursiveIn.mono hO hf

theorem transfer {A B : Oracle} {f : α → β}
    (hf : ComputableIn {oracleFunction A} f) (hAB : Reduces A B) :
    ComputableIn {oracleFunction B} f := by
  apply RecursiveIn.subst hf
  intro g hg
  rw [Set.mem_singleton_iff.mp hg]
  exact hAB

theorem jump {A : Oracle} {f : α → β}
    (hf : ComputableIn {oracleFunction A} f) :
    ComputableIn {oracleFunction (OracleJump.jump A)} f :=
  transfer hf (OracleJump.reduces_jump A)

/-- A total typed function on natural numbers can return its encoded output. -/
theorem encode_recursive {f : ℕ → β} (hf : ComputableIn O f) :
    Nat.RecursiveIn O (fun n => Part.some (encode (f n))) := by
  simpa [ComputableIn, RecursiveIn] using hf

/-- Total decoding is useful for composing numerical oracle programs. -/
def decodeDefault [Inhabited α] (n : ℕ) : α := (decode n).getD default

theorem primrec_decodeDefault [Inhabited α] : Primrec (decodeDefault (α := α)) :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const default)

@[simp] theorem decodeDefault_encode [Inhabited α] (a : α) :
    decodeDefault (encode a) = a := by simp [decodeDefault]

theorem total_decode_recursive [Inhabited α] {f : α → β}
    (hf : ComputableIn O f) :
    Nat.RecursiveIn O (fun n => Part.some (encode (f (decodeDefault n)))) :=
  encode_recursive (comp hf primrec_decodeDefault.computableIn)

/-- Mask invalid codes after proving computation on a total decoder. -/
theorem of_total_decode [Inhabited α] {f : α → β}
    (hf : Nat.RecursiveIn O (fun n => Part.some (encode (f (decodeDefault n))))) :
    ComputableIn O f := by
  have hmask : Partrec (fun n : ℕ => (decode (α := α) n : Part α).map (fun _ => n)) :=
    (Computable.ofOption (Computable.decode (α := α))).map Computable.fst
  change Nat.RecursiveIn O (fun n => Part.bind (decode (α := α) n)
    (fun a => (Part.some (f a)).map encode))
  apply (Nat.RecursiveIn.comp hf (RecursiveIn.iff_nat.mp hmask.recursiveIn)).of_eq
  intro n
  cases hd : decode (α := α) n <;> simp [hd, decodeDefault]

/-- Parameterized finite recursion, with an arbitrary encoded result type. -/
theorem nat_rec [Inhabited α] [Inhabited β]
    {f : α → β} {g : α → ℕ → β → β}
    (hf : ComputableIn O f)
    (hg : ComputableIn O (fun p : α × (ℕ × β) => g p.1 p.2.1 p.2.2)) :
    ComputableIn O (fun p : α × ℕ =>
      Nat.rec (motive := fun _ => β) (f p.1) (fun n v => g p.1 n v) p.2) := by
  let step : ℕ → ℕ → ℕ → ℕ := fun a n v =>
    encode (g (decodeDefault a) n (decodeDefault v))
  have hinput : Primrec (fun p : ℕ =>
      (decodeDefault (α := α) (Nat.unpair p).1,
        ((Nat.unpair (Nat.unpair p).2).1,
          decodeDefault (α := β) (Nat.unpair (Nat.unpair p).2).2))) :=
    (primrec_decodeDefault.comp (Primrec.fst.comp Primrec.unpair)).pair
      ((Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).pair
        (primrec_decodeDefault.comp
          (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))))
  have hs := encode_recursive (comp hg hinput.computableIn)
  have hr := total_prec (g := step) (total_decode_recursive hf) hs
  have hi : Primrec (fun n : ℕ => Nat.pair
      (encode ((decodeDefault (α := α × ℕ) n).1)) (decodeDefault (α := α × ℕ) n).2) :=
    Primrec₂.natPair.comp
      (Primrec.encode.comp (Primrec.fst.comp primrec_decodeDefault))
      (Primrec.snd.comp primrec_decodeDefault)
  apply of_total_decode
  apply (total_comp hr (total_primrec hi)).of_eq
  intro n
  simp only [Nat.unpair_pair, decodeDefault_encode]
  congr 1
  generalize (decodeDefault (α := α × ℕ) n).1 = a
  generalize (decodeDefault (α := α × ℕ) n).2 = k
  induction k with
  | zero => rfl
  | succ k ih =>
    simpa only [step, decodeDefault_encode] using
      congrArg (fun v => step (encode a) k v) ih

/-- A finite table of oracle-computable values uses the same oracle. -/
theorem tabulate [Inhabited α] {f : α → ℕ → β}
    (hf : ComputableIn₂ O f) :
    ComputableIn O (fun p : α × ℕ => (List.range p.2).map (f p.1)) := by
  have hv : ComputableIn O (fun p : α × (ℕ × List β) => f p.1 p.2.1) :=
    comp₂ hf ComputableIn.fst (comp ComputableIn.fst ComputableIn.snd)
  have hs : ComputableIn O (fun p : α × (ℕ × List β) => p.2.2 ++ [f p.1 p.2.1]) :=
    comp₂ Primrec.list_append.computableIn₂ (comp ComputableIn.snd ComputableIn.snd)
      (comp (Primrec.list_cons.comp Primrec.id (Primrec.const [])).computableIn hv)
  have hr := nat_rec (g := fun a n l => l ++ [f a n])
    (ComputableIn.const ([] : List β)) hs
  apply of_eq hr
  intro p
  induction p.2 with
  | zero => rfl
  | succ n ih => simpa only [List.range_succ, List.map_append, List.map_cons, List.map_nil]
      using congrArg (fun l => l ++ [f p.1 n]) ih

end Klr.Computability.RelativeComputable
