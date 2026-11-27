module

public import Klr.PartialBettingCapital

/-!
# Uniform computation of the total rational simulators

The scheduler in `PartialBetting` gives a total strategy for every ordinary
program and either active parity. This module proves that its query and
rational capital are primitive recursive jointly in that program, parity,
and finite transcript. No totality test on the source program is needed.
-/

@[expose] public section

namespace Klr.PartialBetting

open RationalComputability

theorem primrec_approximate_of {α : Type*} [Primcodable α]
    {c : α → Nat.Partrec.Code} {v : α → Assignment} {t : α → ℕ}
    (hc : Primrec c) (hv : Primrec v) (ht : Primrec t) :
    Primrec (fun a => approximate (c a) (v a) (t a)) := by
  have hans : Primrec (fun a => (v a).map Prod.snd) :=
    Primrec.list_map hv (Primrec.snd.comp Primrec.snd).to₂
  exact Primrec.option_map
    (Nat.Partrec.Code.primrec_evaln.comp ((ht.pair hc).pair (Primrec.encode.comp hans)))
    ((Primrec.ofNat Action).comp Primrec.snd).to₂

theorem primrec_filler_of {α : Type*} [Primcodable α]
    {side : α → Bool} {xs : α → Assignment}
    (hside : Primrec side) (hxs : Primrec xs) :
    Primrec (fun a => filler (side a) (xs a)) :=
  Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 2) (primrec_bound.comp hxs))
    ((Primrec.dom_bool fun side => if side then (0 : ℕ) else 1).comp hside)

theorem primrec_query_of {α : Type*} [Primcodable α]
    {c : α → Nat.Partrec.Code} {side : α → Bool} {s : α → State}
    (hc : Primrec c) (hside : Primrec side) (hs : Primrec s) :
    Primrec (fun a => query (c a) (side a) (s a)) := by
  have hplan := primrec_approximate_of hc (Primrec.fst.comp hs)
    (Primrec.snd.comp (Primrec.snd.comp hs))
  have hfill := primrec_filler_of hside (Primrec.fst.comp (Primrec.snd.comp hs))
  have hready : Primrec (fun p : α × Action =>
      match lookup p.2.1 (s p.1).2.1 with
      | none => p.2.1
      | some _ => filler (side p.1) (s p.1).2.1) := by
    apply (Primrec.option_casesOn
      (primrec_lookup.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp (hs.comp Primrec.fst))))
      (Primrec.fst.comp Primrec.snd)
      (hfill.comp (Primrec.fst.comp Primrec.fst)).to₂).of_eq
    intro p
    cases lookup p.2.1 (s p.1).2.1 <;> rfl
  apply (Primrec.option_casesOn hplan hfill hready.to₂).of_eq
  intro a
  unfold query
  cases approximate (c a) (s a).1 (s a).2.2 <;> rfl

theorem primrec_advance_of {α : Type*} [Primcodable α]
    {c : α → Nat.Partrec.Code} {side : α → Bool} {s : α → State} {b : α → Bool}
    (hc : Primrec c) (hside : Primrec side) (hs : Primrec s) (hb : Primrec b) :
    Primrec (fun a => advance (c a) (side a) (s a) (b a)) := by
  have hquery := primrec_query_of hc hside hs
  have hcache : Primrec (fun a => (query (c a) (side a) (s a), b a) :: (s a).2.1) :=
    Primrec.list_cons.comp (hquery.pair hb) (Primrec.fst.comp (Primrec.snd.comp hs))
  have hplan := primrec_approximate_of hc (Primrec.fst.comp hs)
    (Primrec.snd.comp (Primrec.snd.comp hs))
  have hwait : Primrec (fun a => ((s a).1,
      (query (c a) (side a) (s a), b a) :: (s a).2.1, (s a).2.2 + 1)) :=
    (Primrec.fst.comp hs).pair
      (hcache.pair (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp hs))))
  have hanswer : Primrec (fun p : α × Action =>
      (lookup p.2.1 (s p.1).2.1).getD (b p.1)) :=
    Primrec.option_getD.comp
      (primrec_lookup.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp (hs.comp Primrec.fst))))
      (hb.comp Primrec.fst)
  have hready : Primrec (fun p : α × Action =>
      ((s p.1).1 ++ [(p.2.1, (lookup p.2.1 (s p.1).2.1).getD (b p.1))],
        (query (c p.1) (side p.1) (s p.1), b p.1) :: (s p.1).2.1, 0)) :=
    (Primrec.list_concat.comp (Primrec.fst.comp (hs.comp Primrec.fst))
      ((Primrec.fst.comp Primrec.snd).pair hanswer)).pair
      ((hcache.comp Primrec.fst).pair (Primrec.const 0))
  apply (Primrec.option_casesOn hplan hwait hready.to₂).of_eq
  intro a
  unfold advance
  cases approximate (c a) (s a).1 (s a).2.2 <;> rfl

theorem primrec_state_uniform :
    Primrec (fun p : (Nat.Partrec.Code × Bool) × List Bool => state p.1.1 p.1.2 p.2) :=
  Primrec.list_foldl Primrec.snd (Primrec.const initial)
    (primrec_advance_of
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

/-- The actual scan query is primitive recursive jointly in code, side, and
finite answer transcript. -/
theorem primrec_scan_query_uniform :
    Primrec (fun p : (Nat.Partrec.Code × Bool) × List Bool =>
      (scan p.1.1 p.1.2).query p.2) :=
  primrec_query_of (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
    primrec_state_uniform

theorem primrec_wager_of {α : Type*} [Primcodable α]
    {c : α → Nat.Partrec.Code} {side : α → Bool} {s : α → State}
    (hc : Primrec c) (hside : Primrec side) (hs : Primrec s) :
    Primrec (fun a => wager (c a) (side a) (s a)) := by
  have hplan := primrec_approximate_of hc (Primrec.fst.comp hs)
    (Primrec.snd.comp (Primrec.snd.comp hs))
  have hbet : Primrec (fun p : α × Action =>
      if p.2.1.bodd = side p.1 then fraction p.2 else 0) :=
    Primrec.ite (Primrec.eq.comp
      (Primrec.nat_bodd.comp (Primrec.fst.comp Primrec.snd)) (hside.comp Primrec.fst))
      (primrec_fraction.comp Primrec.snd) (Primrec.const 0)
  have hready : Primrec (fun p : α × Action =>
      match lookup p.2.1 (s p.1).2.1 with
      | some _ => 0
      | none => if p.2.1.bodd = side p.1 then fraction p.2 else 0) := by
    apply (Primrec.option_casesOn
      (primrec_lookup.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp (hs.comp Primrec.fst))))
      hbet (Primrec.const 0).to₂).of_eq
    intro p
    cases lookup p.2.1 (s p.1).2.1 <;> rfl
  apply (Primrec.option_casesOn hplan (Primrec.const 0) hready.to₂).of_eq
  intro a
  unfold wager
  cases approximate (c a) (s a).1 (s a).2.2 <;> rfl

theorem primrec_accountStep_of {α : Type*} [Primcodable α]
    {c : α → Nat.Partrec.Code} {side : α → Bool}
    {p : α → State × ℚ} {b : α → Bool}
    (hc : Primrec c) (hside : Primrec side) (hp : Primrec p) (hb : Primrec b) :
    Primrec (fun a => accountStep (c a) (side a) (p a) (b a)) :=
  (primrec_advance_of hc hside (Primrec.fst.comp hp) hb).pair
    (primrec_rat_mul.comp (Primrec.snd.comp hp)
      (primrec_factor.comp (primrec_wager_of hc hside (Primrec.fst.comp hp)) hb))

theorem primrec_account_uniform :
    Primrec (fun p : (Nat.Partrec.Code × Bool) × List Bool => account p.1.1 p.1.2 p.2) :=
  Primrec.list_foldl Primrec.snd (Primrec.const (initial, (1 : ℚ)))
    (primrec_accountStep_of
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

/-- The exact rational capital is uniformly primitive recursive, including
the program index as an input. -/
theorem primrec_rationalCapital_uniform :
    Primrec (fun p : (Nat.Partrec.Code × Bool) × List Bool =>
      rationalCapital p.1.1 p.1.2 p.2) :=
  Primrec.snd.comp primrec_account_uniform

end Klr.PartialBetting
