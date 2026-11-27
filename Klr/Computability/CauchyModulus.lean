module

public import Klr.Computability.ArithmeticSelection
public import Klr.Computability.JumpProperties
public import Klr.ComputableRational
public import Mathlib.Topology.MetricSpace.Cauchy

/-!
# One-jump Cauchy moduli for rational distance tables

If the distances within each of a countable family of sequences are uniformly
oracle-computable rationals, their Cauchy moduli are computable in one jump.
The search decides one universal tail condition and selects its least witness.
Analytic convergence supplies termination and then bounds the distance to the
limit; no effective rate is assumed in that convergence hypothesis.
-/

@[expose] public section

namespace Klr.Computability.CauchyModulus

open ArithmeticHierarchy RationalComputability Filter
open scoped Topology

local instance : Encodable ℚ := (inferInstance : Primcodable ℚ).toEncodable

def dyadic (k : ℕ) : ℚ := (1 / 2 : ℚ) ^ k

theorem primrec_dyadic : Primrec dyadic := by
  have h := primrec_rat_inv.comp (primrec_rat_natCast.comp
    ((Primrec₂.unpaired'.mp Nat.Primrec.pow).comp (Primrec.const 2) Primrec.id))
  exact h.of_eq fun _ => by simp [dyadic, one_div, inv_pow]

private def rational (n : ℕ) : ℚ := (Encodable.decode n).getD 0

private theorem primrec_rational : Primrec rational :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const 0)

@[simp] private theorem rational_encode (q : ℚ) : rational (Encodable.encode q) = q := by
  simp [rational]

/-- The entire tail has the prescribed rational diameter. -/
def Tail (d : ℕ → ℕ → ℕ → ℚ) (i k N : ℕ) : Prop :=
  ∀ s t, N ≤ s → N ≤ t → d i s t ≤ dyadic k

private def matrix (d : ℕ → ℕ → ℕ → ℚ) (z : ℕ) : Prop :=
  let x := Nat.unpair (Nat.unpair z).1
  let p := Nat.unpair x.1
  let st := Nat.unpair (Nat.unpair z).2
  x.2 ≤ st.1 → x.2 ≤ st.2 → d p.1 st.1 st.2 ≤ dyadic p.2

/-- A single finite comparison is decidable in the distance table's oracle. -/
private theorem matrix_recursive {A : Oracle} {d : ℕ → ℕ → ℕ → ℚ}
    (hd : ComputableIn {oracleFunction A}
      (fun p : ℕ × (ℕ × ℕ) => d p.1 p.2.1 p.2.2)) :
    RecursivePred A (matrix d) := by
  classical
  have hd' : Nat.RecursiveIn {oracleFunction A} (fun z => Part.some
      (Encodable.encode (d (Nat.unpair z).1 (Nat.unpair (Nat.unpair z).2).1
        (Nat.unpair (Nat.unpair z).2).2))) := by
    simpa [ComputableIn, RecursiveIn, Encodable.decode_prod_val] using hd
  let l : ℕ → ℕ := fun z => (Nat.unpair z).1
  let r : ℕ → ℕ := fun z => (Nat.unpair z).2
  have hl : Primrec l := Primrec.fst.comp Primrec.unpair
  have hr : Primrec r := Primrec.snd.comp Primrec.unpair
  have hi := hl.comp (hl.comp hl)
  have hk := hr.comp (hl.comp hl)
  have hN := hr.comp hl
  have hs := hl.comp hr
  have ht := hr.comp hr
  have harg := Primrec₂.natPair.comp hi (Primrec₂.natPair.comp hs ht)
  have hvalue := total_comp hd' (total_primrec harg)
  have hinput := total_pair (total_primrec Primrec.id) hvalue
  have hcheck : Primrec (fun u : ℕ =>
      if r (l (l u)) ≤ l (r (l u)) ∧ r (l (l u)) ≤ r (r (l u)) then
        if rational (r u) ≤ dyadic (r (l (l (l u)))) then 1 else 0
      else 1) :=
    Primrec.ite
      ((Primrec.nat_le.comp (hN.comp hl) (hs.comp hl)).and
        (Primrec.nat_le.comp (hN.comp hl) (ht.comp hl)))
      (Primrec.ite (primrec_rat_le.comp (primrec_rational.comp hr)
        (primrec_dyadic.comp (hk.comp hl))) (Primrec.const 1) (Primrec.const 0))
      (Primrec.const 1)
  apply (total_comp (total_primrec hcheck) hinput).of_eq
  intro z
  simp only [l, r, Nat.unpair_pair, rational_encode, matrix]
  split_ifs <;> simp_all

/-- The universal Cauchy-tail condition is decidable in one jump. -/
theorem tail_recursive_jump {A : Oracle} {d : ℕ → ℕ → ℕ → ℚ}
    (hd : ComputableIn {oracleFunction A}
      (fun p : ℕ × (ℕ × ℕ) => d p.1 p.2.1 p.2.2)) :
    RecursivePred (OracleJump.jump A) (fun z =>
      Tail d (Nat.unpair (Nat.unpair z).1).1 (Nat.unpair (Nat.unpair z).1).2
        (Nat.unpair z).2) := by
  apply Form.congr (n := 0) (s := true)
    (OracleJump.forall_recursive_jump (matrix_recursive hd))
  intro z
  simp only [matrix, Nat.unpair_pair, Tail]
  constructor
  · intro h s t
    simpa only [Nat.unpair_pair] using h (Nat.pair s t)
  · intro h a
    exact h (Nat.unpair a).1 (Nat.unpair a).2

/-- An analytically Cauchy rational distance family has a uniform modulus
computable in the jump of the distance oracle. -/
theorem exists_modulus {A : Oracle} {d : ℕ → ℕ → ℕ → ℚ}
    (hd : ComputableIn {oracleFunction A}
      (fun p : ℕ × (ℕ × ℕ) => d p.1 p.2.1 p.2.2))
    (hC : ∀ i k, ∃ N, Tail d i k N) :
    ∃ m : ℕ → ℕ → ℕ, ComputableIn₂ {oracleFunction (OracleJump.jump A)} m ∧
      ∀ i k, Tail d i k (m i k) := by
  let P : ℕ → Prop := fun z =>
    Tail d (Nat.unpair (Nat.unpair z).1).1 (Nat.unpair (Nat.unpair z).1).2
      (Nat.unpair z).2
  have htotal : ∀ x, ∃ N, P (Nat.pair x N) := by
    intro x
    simpa only [P, Nat.unpair_pair] using hC (Nat.unpair x).1 (Nat.unpair x).2
  let f := ArithmeticSelection.least P htotal
  have hf := ArithmeticSelection.least_recursive (tail_recursive_jump hd) htotal
  let m : ℕ → ℕ → ℕ := fun i k => f (Nat.pair i k)
  refine ⟨m, ?_, fun i k => ?_⟩
  · simpa [ComputableIn₂, ComputableIn, RecursiveIn, Encodable.decode_prod_val,
      m, f, Nat.pair_unpair] using hf
  · simpa only [P, m, f, Nat.unpair_pair] using
      ArithmeticSelection.least_spec P htotal (Nat.pair i k)

/-- The rational table may present the actual distances in any pseudometric
space; only the table, not the ambient space, needs an encoding. -/
theorem exists_modulus_of_cauchySeq {A : Oracle} {E : Type*} [PseudoMetricSpace E]
    {a : ℕ → ℕ → E} {d : ℕ → ℕ → ℕ → ℚ}
    (hd : ComputableIn {oracleFunction A}
      (fun p : ℕ × (ℕ × ℕ) => d p.1 p.2.1 p.2.2))
    (hdist : ∀ i s t, dist (a i s) (a i t) = (d i s t : ℝ))
    (hC : ∀ i, CauchySeq (a i)) :
    ∃ m : ℕ → ℕ → ℕ, ComputableIn₂ {oracleFunction (OracleJump.jump A)} m ∧
      ∀ i k s t, m i k ≤ s → m i k ≤ t →
        dist (a i s) (a i t) ≤ (1 / 2 : ℝ) ^ k := by
  have htail : ∀ i k, ∃ N, Tail d i k N := by
    intro i k
    obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp (hC i)) ((1 / 2 : ℝ) ^ k) (by positivity)
    refine ⟨N, fun s t hs ht => ?_⟩
    apply (Rat.cast_le (K := ℝ)).mp
    simpa only [← hdist, dyadic, Rat.cast_pow, Rat.cast_div, Rat.cast_one,
      Rat.cast_ofNat] using (hN s hs t ht).le
  obtain ⟨m, hm, hspec⟩ := exists_modulus hd htail
  refine ⟨m, hm, fun i k s t hs ht => ?_⟩
  have h := (Rat.cast_le (K := ℝ)).mpr (hspec i k s t hs ht)
  simpa only [← hdist, dyadic, Rat.cast_pow, Rat.cast_div, Rat.cast_one,
    Rat.cast_ofNat] using h

/-- An ordinary convergence proof suffices to obtain uniformly accurate
indices in one jump. No modulus of the given convergence is an assumption. -/
theorem exists_limit_modulus {A : Oracle} {E : Type*} [PseudoMetricSpace E]
    {a : ℕ → ℕ → E} {d : ℕ → ℕ → ℕ → ℚ} {l : ℕ → E}
    (hd : ComputableIn {oracleFunction A}
      (fun p : ℕ × (ℕ × ℕ) => d p.1 p.2.1 p.2.2))
    (hdist : ∀ i s t, dist (a i s) (a i t) = (d i s t : ℝ))
    (hlim : ∀ i, Tendsto (a i) atTop (𝓝 (l i))) :
    ∃ m : ℕ → ℕ → ℕ, ComputableIn₂ {oracleFunction (OracleJump.jump A)} m ∧
      ∀ i k, dist (a i (m i k)) (l i) ≤ (1 / 2 : ℝ) ^ k := by
  obtain ⟨m, hm, hspec⟩ := exists_modulus_of_cauchySeq hd hdist
    (fun i => (hlim i).cauchySeq)
  refine ⟨m, hm, fun i k => ?_⟩
  apply le_of_tendsto (tendsto_const_nhds.dist (hlim i))
  exact eventually_atTop.mpr ⟨m i k, fun t ht => hspec i k (m i k) t le_rfl ht⟩

end Klr.Computability.CauchyModulus
