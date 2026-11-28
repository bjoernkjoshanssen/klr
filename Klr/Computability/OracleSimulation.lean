module

public import Klr.Computability.OracleCode
public import Klr.Computability.RelativeSearch

/-!
# Finite simulation of oracle computations

A terminating relative computation uses only a finite oracle prefix. The
`Approximates` relation records soundness and eventual completeness of such
finite approximations. The numerical `trial` evaluator bounds both the oracle
prefix and the ordinary evaluation bound; its total evaluation is recursive in
the oracle, uniformly in the source code, input, and finite bounds.

Adapted from the Apache-2.0 `bjoernkjoshanssen/tt-auto` project, commit
`3190d8d1a78e709297423d1343f68395127be5de`, using `Effective/FiniteApproximation.lean`,
`Effective/UniformOracle.lean`, and the finite trial API of
`OrdinalCodes/IndexMatrix.lean`. Unrelated branch, degree, and model machinery
has been removed.
-/

@[expose] public section

namespace Klr.Computability

def Approximates {α : Type*} (p : Part α) (ps : ℕ → Part α) : Prop :=
  (∀ m a, a ∈ ps m → a ∈ p) ∧
  (∀ a, a ∈ p → ∃ M, ∀ m, M ≤ m → a ∈ ps m)

namespace Approximates
variable {α β : Type*}

theorem const (p : Part α) : Approximates p (fun _ => p) :=
  ⟨fun _ _ h => h, fun _ h => ⟨0,fun _ _ => h⟩⟩

theorem bind {p : Part α} {ps : ℕ → Part α} {f : α → Part β}
    {fs : ℕ → α → Part β} (hp : Approximates p ps)
    (hf : ∀ a, Approximates (f a) (fun m => fs m a)) :
    Approximates (p.bind f) (fun m => (ps m).bind (fs m)) := by
  constructor
  · intro m b hb
    obtain ⟨a,ha,hb⟩ := Part.mem_bind_iff.mp hb
    exact Part.mem_bind_iff.mpr ⟨a,hp.1 m a ha,(hf a).1 m b hb⟩
  · intro b hb
    obtain ⟨a,ha,hb⟩ := Part.mem_bind_iff.mp hb
    obtain ⟨M,hM⟩ := hp.2 a ha
    obtain ⟨N,hN⟩ := (hf a).2 b hb
    exact ⟨max M N,fun m hm => Part.mem_bind_iff.mpr
      ⟨a,hM m ((le_max_left _ _).trans hm),hN m ((le_max_right _ _).trans hm)⟩⟩

theorem map {p : Part α} {ps : ℕ → Part α} (hp : Approximates p ps) (f : α → β) :
    Approximates (p.map f) (fun m => (ps m).map f) := by
  simpa only [Part.bind_some_eq_map] using hp.bind (fun a => const (Part.some (f a)))

theorem finite_bounds (P : ℕ → ℕ → Prop) (n : ℕ)
    (h : ∀ i, i < n → ∃ M, ∀ m, M ≤ m → P i m) :
    ∃ M, ∀ m, M ≤ m → ∀ i, i < n → P i m := by
  induction n with
  | zero => exact ⟨0,by simp⟩
  | succ n ih =>
    obtain ⟨M,hM⟩ := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    obtain ⟨N,hN⟩ := h n (Nat.lt_succ_self n)
    refine ⟨max M N, fun m hm i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact hM m ((le_max_left _ _).trans hm) i hi
    · exact hN m ((le_max_right _ _).trans hm)

theorem rfind {p : ℕ → Part Bool} {ps : ℕ → ℕ → Part Bool}
    (hp : ∀ n, Approximates (p n) (fun m => ps m n)) :
    Approximates (Nat.rfind p) (fun m => Nat.rfind (ps m)) := by
  constructor
  · intro m n hn
    obtain ⟨ht,hf⟩ := Nat.mem_rfind.mp hn
    exact Nat.mem_rfind.mpr ⟨(hp n).1 m true ht,fun {k} hk => (hp k).1 m false (hf hk)⟩
  · intro n hn
    obtain ⟨ht,hf⟩ := Nat.mem_rfind.mp hn
    obtain ⟨M,hM⟩ := (hp n).2 true ht
    obtain ⟨N,hN⟩ := finite_bounds (fun k m => false ∈ ps m k) n
      (fun k hk => (hp k).2 false (hf hk))
    exact ⟨max M N, fun m hm => Nat.mem_rfind.mpr
      ⟨hM m ((le_max_left _ _).trans hm),fun {k} hk => hN m ((le_max_right _ _).trans hm) k hk⟩⟩
end Approximates

namespace OracleCode

theorem eval_approximates {g : ℕ →. ℕ} {gs : ℕ → ℕ →. ℕ}
    (hg : ∀ n, Approximates (g n) (fun m => gs m n)) (c : OracleCode) :
    ∀ n, Approximates (eval g c n) (fun m => eval (gs m) c n) := by
  induction c with
  | zero => intro n; exact Approximates.const _
  | succ => intro n; exact Approximates.const _
  | left => intro n; exact Approximates.const _
  | right => intro n; exact Approximates.const _
  | query => exact hg
  | pair c d hc hd =>
    intro n
    exact (hc n).bind (fun a => (hd n).map (Nat.pair a))
  | comp c d hc hd => intro n; exact (hd n).bind hc
  | prec c d hc hd =>
    intro p
    have hr : ∀ k, Approximates
        (Nat.rec (eval g c (Nat.unpair p).1)
          (fun y ih => ih.bind (fun i => eval g d (Nat.pair (Nat.unpair p).1 (Nat.pair y i)))) k)
        (fun m => Nat.rec (eval (gs m) c (Nat.unpair p).1)
          (fun y ih => ih.bind (fun i =>
            eval (gs m) d (Nat.pair (Nat.unpair p).1 (Nat.pair y i)))) k) := by
      intro k
      induction k with
      | zero => exact hc _
      | succ k ih => exact ih.bind (fun i => hd _)
    exact hr _
  | find c hc =>
    intro n
    exact Approximates.rfind (fun k => (hc (Nat.pair n k)).map (fun m => decide (m=0)))

end OracleCode

namespace OracleSimulation

open Encodable

/-- A finite oracle is undefined beyond its recorded prefix. -/
def lookup (L : List ℕ) (k : ℕ) : Part ℕ := (L[k]? : Part ℕ)

theorem lookup_partrec : Partrec₂ lookup :=
  Computable.ofOption Primrec.list_getElem?.to_comp

def oraclePrefix (g : ℕ → ℕ) (m : ℕ) : List ℕ := (List.range m).map g

def appendEncoded (a b : ℕ) : ℕ := encode ((decode (α := List ℕ) a).getD [] ++ [b])

theorem appendEncoded_primrec : Primrec₂ appendEncoded :=
  Primrec.encode.comp (Primrec.list_append.comp
    (Primrec.option_getD_default.comp (Primrec.decode.comp Primrec.fst))
    (Primrec.list_cons.comp Primrec.snd (Primrec.const [])))

theorem prefix_recursive (g : ℕ → ℕ) :
    Nat.RecursiveIn {fun n => Part.some (g n)}
      (fun m => Part.some (encode (oraclePrefix g m))) := by
  have hquery : Nat.RecursiveIn {fun n => Part.some (g n)} (fun n => Part.some (g n)) :=
    .oracle _ (Set.mem_singleton _)
  have hy := total_primrec (O := {fun n => Part.some (g n)})
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
  have hi := total_primrec (O := {fun n => Part.some (g n)})
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
  have hs := total_comp (total_primrec (O := {fun n => Part.some (g n)})
    (appendEncoded_primrec.comp (Primrec.fst.comp Primrec.unpair)
      (Primrec.snd.comp Primrec.unpair)))
    (total_pair hi (total_comp hquery hy))
  have hp := Nat.RecursiveIn.prec (total_primrec (O := {fun n => Part.some (g n)})
    (Primrec.const (encode ([] : List ℕ)))) hs
  have hh := Nat.RecursiveIn.comp hp
    (total_pair (total_primrec (O := {fun n => Part.some (g n)}) (Primrec.const 0))
      (total_primrec (O := {fun n => Part.some (g n)}) Primrec.id))
  apply hh.of_eq
  intro n
  change (Part.some (Nat.pair 0 n)).bind _ = _
  rw [Part.bind_some]
  simp only [Nat.unpair_pair]
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ih]
    simp [appendEncoded, oraclePrefix, List.range_succ]

theorem prefix_approximates (g : ℕ → ℕ) (k : ℕ) :
    Approximates (Part.some (g k)) (fun m => lookup (oraclePrefix g m) k) := by
  have he (m : ℕ) : (oraclePrefix g m)[k]? = if k < m then some (g k) else none := by
    simp only [oraclePrefix, List.getElem?_map]
    by_cases hk : k < m
    · rw [List.getElem?_range hk, ite_eq_left hk]
      rfl
    · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hk), ite_eq_right hk]
      rfl
  constructor
  · intro m a ha
    change a ∈ ((oraclePrefix g m)[k]? : Part ℕ) at ha
    rw [he] at ha
    split at ha
    · simpa using ha
    · simp at ha
  · intro a ha
    have ha' : a = g k := Part.mem_some_iff.mp ha
    subst a
    refine ⟨k+1,fun m hm => ?_⟩
    change g k ∈ ((oraclePrefix g m)[k]? : Part ℕ)
    rw [he, ite_eq_left (by omega)]
    exact Part.mem_some _


def trial (g : ℕ → ℕ) (c : Nat.Partrec.Code) (n z : ℕ) : Option ℕ :=
  c.evaln (Nat.unpair z).2 (Nat.pair (encode (oraclePrefix g (Nat.unpair z).1)) n)

theorem trial_recursive (g : ℕ → ℕ) (c : Nat.Partrec.Code) :
    Nat.RecursiveIn {fun n => Part.some (g n)}
      (fun z => Part.some (encode (trial g c (Nat.unpair z).1 (Nat.unpair z).2))) := by
  have hm := total_primrec (O := {fun n => Part.some (g n)})
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
  have hk := total_primrec (O := {fun n => Part.some (g n)})
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
  have hn := (total_primrec (O := {fun n => Part.some (g n)})) (Primrec.fst.comp Primrec.unpair)
  have hp := total_comp (prefix_recursive g) hm
  have he := (total_primrec (O := {fun n => Part.some (g n)})) (Primrec.encode.comp
    (Nat.Partrec.Code.primrec_evaln.comp
      (((Primrec.fst.comp Primrec.unpair).pair (Primrec.const c)).pair
        (Primrec.snd.comp Primrec.unpair))))
  exact (total_comp he (total_pair hk (total_pair hp hn))).of_eq (fun z => by
    simp [trial])

theorem compute_of_finite (g f : ℕ → ℕ) (c : Nat.Partrec.Code)
    (ha : ∀ n, Approximates (Part.some (f n))
      (fun m => c.eval (Nat.pair (encode (oraclePrefix g m)) n))) :
    Nat.RecursiveIn {fun n => Part.some (g n)} (fun n => Part.some (f n)) := by
  apply total_search (trial_recursive g c) f
  · intro n z a h
    exact Part.mem_some_iff.mp ((ha n).1 (Nat.unpair z).1 a
      (Nat.Partrec.Code.evaln_sound h))
  · intro n
    obtain ⟨M,hM⟩ := (ha n).2 (f n) (Part.mem_some _)
    obtain ⟨k,hk⟩ := Nat.Partrec.Code.evaln_complete.mp (hM M le_rfl)
    exact ⟨Nat.pair M k,f n,by simpa [trial] using hk⟩


/-- One finite trial relative to a Boolean oracle. -/
def run (A : Oracle) (c : Nat.Partrec.Code) (n z : ℕ) : Option ℕ :=
  trial (fun k => bit (A k)) c n z

def machine (e : ℕ) : Nat.Partrec.Code := (decode e).getD .zero

theorem machine_primrec : Primrec machine :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const Nat.Partrec.Code.zero)

@[simp] theorem machine_encode (d : Nat.Partrec.Code) : machine (encode d) = d := by
  simp [machine]

theorem run_uniform_recursive (Y : Oracle) :
    Nat.RecursiveIn {oracleFunction Y} (fun v => Part.some
      (encode (run Y (machine (Nat.unpair v).1)
        (Nat.unpair (Nat.unpair v).2).1 (Nat.unpair (Nat.unpair v).2).2))) := by
  let O : Set (ℕ →. ℕ) := {oracleFunction Y}
  let e := Primrec.fst.comp Primrec.unpair
  let rest := Primrec.snd.comp Primrec.unpair
  let n := Primrec.fst.comp (Primrec.unpair.comp rest)
  let z := Primrec.snd.comp (Primrec.unpair.comp rest)
  have he := total_primrec (O := O) e
  have hn := total_primrec (O := O) n
  have hm := total_primrec (O := O) (Primrec.fst.comp (Primrec.unpair.comp z))
  have ht := total_primrec (O := O) (Primrec.snd.comp (Primrec.unpair.comp z))
  have hL := total_comp (prefix_recursive (fun k => bit (Y k))) hm
  let r := Primrec.snd.comp Primrec.unpair
  have hdecode := total_primrec (O := O) (Primrec.encode.comp (Nat.Partrec.Code.primrec_evaln.comp
    (((Primrec.fst.comp Primrec.unpair).pair
      (machine_primrec.comp (Primrec.fst.comp (Primrec.unpair.comp r)))).pair
      (Primrec.snd.comp (Primrec.unpair.comp r)))))
  exact (total_comp hdecode (total_pair ht (total_pair he (total_pair hL hn)))).of_eq
    (fun v => by simp [run, trial])


end OracleSimulation

end Klr.Computability
