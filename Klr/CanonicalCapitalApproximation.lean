module

public import Klr.ComputableRational
public import Klr.Computability.ArithmeticSelection
public import Klr.Computability.JumpProperties

/-!
# Canonical programs for rational approximation

A computable real capital function has an ordinary program producing rational
approximations at the prescribed dyadic precision. We choose the least index
of such a program. For a uniformly computable family of rational capital
functions, validity of an index is a relative-free Π₂ predicate, so the chosen
indices are uniformly computable in the second jump.

This canonical choice lets the existing normalization API retain its exact
type while giving its choices a proved uniform complexity bound. The query
rules are unaffected by the choice of capital approximation.
-/

@[expose] public section

namespace Klr.CanonicalCapitalApproximation

open RationalComputability _root_.Klr.Computability
open _root_.Klr.Computability.ArithmeticHierarchy

local instance : Encodable ℚ := (inferInstance : Primcodable ℚ).toEncodable

def input (n : ℕ) : List Bool × ℕ :=
  (Encodable.decode n).getD ([], 0)

def rational (n : ℕ) : ℚ := (Encodable.decode n).getD 0

theorem primrec_input : Primrec input :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const ([], 0))

theorem primrec_rational : Primrec rational :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const 0)

@[simp] theorem input_encode (p : List Bool × ℕ) : input (Encodable.encode p) = p := by
  simp [input]

@[simp] theorem rational_encode (q : ℚ) : rational (Encodable.encode q) = q := by
  simp [rational]

/-- One finite program execution certifies a sufficiently accurate answer. -/
def Verified (d : List Bool → ℝ) (e u k : ℕ) : Prop :=
  ∃ v, v ∈ (OracleSimulation.machine e).evaln k u ∧
    |(rational v : ℝ) - d (input u).1| ≤ (1 / 2 : ℝ) ^ (input u).2

/-- A total ordinary program approximating the specified capital function. -/
def Good (d : List Bool → ℝ) (e : ℕ) : Prop :=
  ∀ u, ∃ k, Verified d e u k

theorem exists_good (d : List Bool → ℝ) (hd : ComputableRealCapital d) :
    ∃ e, Good d e := by
  obtain ⟨q, hq, herror⟩ := hd
  have hq' : Computable (fun p : List Bool × ℕ => q p.1 p.2) :=
    computable_rat_of_numDen hq
  have hc : Computable (fun u => Encodable.encode (q (input u).1 (input u).2)) :=
    Computable.encode.comp (hq'.comp primrec_input.to_comp)
  obtain ⟨c, hc⟩ := partrec_code hc
  refine ⟨Encodable.encode c, fun u => ?_⟩
  have hm : Encodable.encode (q (input u).1 (input u).2) ∈ c.eval u := by
    simpa using (hc u).symm ▸ (Part.mem_some (Encodable.encode (q (input u).1 (input u).2)))
  obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hm
  exact ⟨k, _, by simpa using hk, by simpa using herror (input u).1 (input u).2⟩

/-- The least valid program index; the correctness proof does not determine it. -/
noncomputable def index (d : List Bool → ℝ) (hd : ComputableRealCapital d) : ℕ := by
  classical
  exact Nat.find (exists_good d hd)

theorem good_index (d : List Bool → ℝ) (hd : ComputableRealCapital d) :
    Good d (index d hd) := by
  classical
  exact Nat.find_spec (exists_good d hd)

theorem output_exists (d : List Bool → ℝ) (hd : ComputableRealCapital d) (u : ℕ) :
    ∃ v, v ∈ (OracleSimulation.machine (index d hd)).eval u := by
  obtain ⟨k, v, hv, _⟩ := good_index d hd u
  exact ⟨v, Nat.Partrec.Code.evaln_sound hv⟩

/-- The uniquely determined output of the selected total program. -/
noncomputable def output (d : List Bool → ℝ) (hd : ComputableRealCapital d) (u : ℕ) : ℕ :=
  (output_exists d hd u).choose

theorem output_mem (d : List Bool → ℝ) (hd : ComputableRealCapital d) (u : ℕ) :
    output d hd u ∈ (OracleSimulation.machine (index d hd)).eval u :=
  (output_exists d hd u).choose_spec

theorem computable_output (d : List Bool → ℝ) (hd : ComputableRealCapital d) :
    Computable (output d hd) :=
  (Nat.Partrec.Code.eval_part.comp (Computable.const (OracleSimulation.machine (index d hd)))
    Computable.id).of_eq_tot (output_mem d hd)

/-- The canonical rational approximation at one transcript and precision. -/
noncomputable def value (d : List Bool → ℝ) (hd : ComputableRealCapital d)
    (v : List Bool) (n : ℕ) : ℚ :=
  rational (output d hd (Encodable.encode (v, n)))

theorem computable_value (d : List Bool → ℝ) (hd : ComputableRealCapital d) :
    Computable (fun p : List Bool × ℕ => value d hd p.1 p.2) :=
  primrec_rational.to_comp.comp ((computable_output d hd).comp Computable.encode)

theorem error (d : List Bool → ℝ) (hd : ComputableRealCapital d)
    (v : List Bool) (n : ℕ) :
    |(value d hd v n : ℝ) - d v| ≤ (1 / 2 : ℝ) ^ n := by
  obtain ⟨k, a, ha, he⟩ := good_index d hd (Encodable.encode (v, n))
  have ha' : a = output d hd (Encodable.encode (v, n)) :=
    Part.mem_unique (Nat.Partrec.Code.evaln_sound ha) (output_mem d hd _)
  simpa only [ha', input_encode, value] using he

/-- Finite exact-rational check for one proposed approximation output. -/
def check (F : ℕ → List Bool → ℚ) (i e u k : ℕ) : Bool :=
  ((OracleSimulation.machine e).evaln k u).any fun v =>
    decide (|rational v - F i (input u).1| ≤ (1 / 2 : ℚ) ^ (input u).2)

theorem check_eq_true (F : ℕ → List Bool → ℚ) (i e u k : ℕ) :
    check F i e u k = true ↔ Verified (fun v => (F i v : ℝ)) e u k := by
  unfold check Verified
  simp only [Option.any_eq_true, decide_eq_true_eq, Option.mem_def]
  apply exists_congr
  intro a
  apply and_congr_right
  intro _
  simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_pow, Rat.cast_div,
    Rat.cast_one, Rat.cast_ofNat] using
    (Rat.cast_le (K := ℝ) (p := |rational a - F i (input u).1|)
      (q := (1 / 2 : ℚ) ^ (input u).2)).symm

theorem computable_check (F : ℕ → List Bool → ℚ) (hF : Computable₂ F) :
    Computable (fun z : ((ℕ × ℕ) × ℕ) × ℕ =>
      check F z.1.1.1 z.1.1.2 z.1.2 z.2) := by
  let hi : Computable (fun z : ((ℕ × ℕ) × ℕ) × ℕ => z.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  let he : Computable (fun z : ((ℕ × ℕ) × ℕ) × ℕ => z.1.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  let hu : Computable (fun z : ((ℕ × ℕ) × ℕ) × ℕ => z.1.2) :=
    Computable.snd.comp Computable.fst
  let hk : Computable (fun z : ((ℕ × ℕ) × ℕ) × ℕ => z.2) := Computable.snd
  have hrun := Nat.Partrec.Code.primrec_evaln.to_comp.comp
    ((hk.pair (OracleSimulation.machine_primrec.to_comp.comp he)).pair hu)
  have hp := primrec_input.to_comp.comp hu
  have hv := hF.comp hi (Computable.fst.comp hp)
  have hprec := Computable.snd.comp hp
  have hpow : Computable (fun z : ((ℕ × ℕ) × ℕ) × ℕ =>
      (1 / 2 : ℚ) ^ (input z.1.2).2) := by
    have h := primrec_rat_inv.to_comp.comp
      (primrec_rat_natCast.to_comp.comp
        ((Primrec₂.unpaired'.mp Nat.Primrec.pow).to_comp.comp (Computable.const 2) hprec))
    exact h.of_eq fun z => by simp [one_div, inv_pow]
  have habs : Computable (fun q : ℚ => |q|) :=
    (primrec_rat_max.to_comp.comp Computable.id primrec_rat_neg.to_comp).of_eq
      fun _ => abs_eq_max_neg.symm
  have hbound : Computable₂ (fun z : ((ℕ × ℕ) × ℕ) × ℕ => fun a : ℕ =>
      decide (|rational a - F z.1.1.1 (input z.1.2).1| ≤
        (1 / 2 : ℚ) ^ (input z.1.2).2)) :=
    primrec_rat_le.decide.to_comp.comp
      (habs.comp (primrec_rat_sub.to_comp.comp
        (primrec_rational.to_comp.comp Computable.snd) (hv.comp Computable.fst)))
      (hpow.comp Computable.fst)
  exact (Computable.option_casesOn hrun (Computable.const false) hbound).of_eq
    fun z => by
      dsimp only [check]
      cases (OracleSimulation.machine z.1.1.2).evaln z.2 z.1.2 <;> rfl

/-- Validity of an approximation index for a uniform rational family is Π₂. -/
theorem good_pi_two (F : ℕ → List Bool → ℚ) (hF : Computable₂ F) :
    Pi zeroOracle 2 (fun z => Good (fun v => (F (Nat.unpair z).1 v : ℝ))
      (Nat.unpair z).2) := by
  let unpack : ℕ → ((ℕ × ℕ) × ℕ) × ℕ := fun z =>
    ((Nat.unpair (Nat.unpair (Nat.unpair z).1).1,
      (Nat.unpair (Nat.unpair z).1).2), (Nat.unpair z).2)
  have hunpack : Primrec unpack :=
    ((Primrec.unpair.comp (Primrec.fst.comp (Primrec.unpair.comp
      (Primrec.fst.comp Primrec.unpair)))).pair
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))).pair
      (Primrec.snd.comp Primrec.unpair)
  let P : ℕ → Prop := fun z =>
    check F (unpack z).1.1.1 (unpack z).1.1.2 (unpack z).1.2 (unpack z).2 = true
  have hcheck := (computable_check F hF).comp hunpack.to_comp
  have hP : RecursivePred zeroOracle P := by
    classical
    exact (total_computable (bit_primrec.to_comp.comp hcheck)).of_eq
      fun z => by
        by_cases hz : check F (unpack z).1.1.1 (unpack z).1.1.2
          (unpack z).1.2 (unpack z).2 = true <;> simp [bit, P, hz]
  apply (forall_form (n := 1) (exists_form (n := 0) hP)).congr
  intro z
  simp only [P, unpack, Nat.unpair_pair, check_eq_true, Good]

/-- Canonical indices for any uniform rational family are second-jump computable. -/
theorem index_recursive (F : ℕ → List Bool → ℚ) (hF : Computable₂ F) :
    Nat.RecursiveIn {oracleFunction (OracleJump.zeroJump 2)} (fun i => Part.some
      (index (fun v => (F i v : ℝ))
        (computableRealCapital_of_rat (hF.comp (Computable.const i) Computable.id)))) := by
  classical
  let P : ℕ → Prop := fun z => Good (fun v => (F (Nat.unpair z).1 v : ℝ))
    (Nat.unpair z).2
  have htotal : ∀ i, ∃ e, P (Nat.pair i e) := by
    intro i
    simpa only [P, Nat.unpair_pair] using exists_good (fun v => (F i v : ℝ))
      (computableRealCapital_of_rat (hF.comp (Computable.const i) Computable.id))
  have h := ArithmeticSelection.least_recursive_of_form (good_pi_two F hF) htotal
  apply h.of_eq
  intro i
  congr 1
  apply Nat.find_congr'
  intro n
  simp only [Nat.unpair_pair]

/-- The canonical index theorem in Mathlib's total relative-computability interface. -/
theorem index_computableIn (F : ℕ → List Bool → ℚ) (hF : Computable₂ F) :
    ComputableIn {oracleFunction (OracleJump.zeroJump 2)} (fun i =>
      index (fun v => (F i v : ℝ))
        (computableRealCapital_of_rat (hF.comp (Computable.const i) Computable.id))) :=
  RecursiveIn.iff_nat.mpr (index_recursive F hF)

/-- Executing the selected ordinary programs costs no additional oracle. -/
theorem output_recursive_of_index {A : Oracle} (d : ℕ → List Bool → ℝ)
    (hd : ∀ i, ComputableRealCapital (d i))
    (hi : Nat.RecursiveIn {oracleFunction A}
      (fun i => Part.some (index (d i) (hd i)))) :
    Nat.RecursiveIn {oracleFunction A} (fun z => Part.some
      (output (d (Nat.unpair z).1) (hd (Nat.unpair z).1) (Nat.unpair z).2)) := by
  have he : Partrec (fun z : ℕ =>
      (OracleSimulation.machine (Nat.unpair z).1).eval (Nat.unpair z).2) :=
    Nat.Partrec.Code.eval_part.comp
      (OracleSimulation.machine_primrec.to_comp.comp
        (Computable.fst.comp Primrec.unpair.to_comp))
      (Computable.snd.comp Primrec.unpair.to_comp)
  have hp := total_pair
    (total_comp hi (total_primrec (Primrec.fst.comp Primrec.unpair)))
    (total_primrec (Primrec.snd.comp Primrec.unpair))
  have h := Nat.RecursiveIn.comp (RecursiveIn.iff_nat.mp he.recursiveIn) hp
  apply h.of_eq_tot
  intro z
  simpa using output_mem (d (Nat.unpair z).1) (hd (Nat.unpair z).1) (Nat.unpair z).2

/-- The canonical rational approximation is uniformly second-jump computable;
the natural input codes the family index and the transcript/precision pair. -/
theorem value_recursive (F : ℕ → List Bool → ℚ) (hF : Computable₂ F) :
    Nat.RecursiveIn {oracleFunction (OracleJump.zeroJump 2)} (fun z => Part.some
      (Encodable.encode (value (fun v => (F (Nat.unpair z).1 v : ℝ))
        (computableRealCapital_of_rat
          (hF.comp (Computable.const (Nat.unpair z).1) Computable.id))
        (input (Nat.unpair z).2).1 (input (Nat.unpair z).2).2))) := by
  let hd := fun i => computableRealCapital_of_rat
    (hF.comp (Computable.const i) Computable.id)
  have hout := output_recursive_of_index (fun i v => (F i v : ℝ)) hd
    (index_recursive F hF)
  have hp : Primrec (fun z : ℕ => Nat.pair (Nat.unpair z).1
      (Encodable.encode (input (Nat.unpair z).2))) :=
    Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair)
      (Primrec.encode.comp (primrec_input.comp (Primrec.snd.comp Primrec.unpair)))
  have hrat : Primrec (fun n => Encodable.encode (rational n)) :=
    Primrec.encode.comp primrec_rational
  exact (total_comp (total_primrec hrat) (total_comp hout (total_primrec hp))).of_eq
    fun z => by simp only [Nat.unpair_pair, value]

end Klr.CanonicalCapitalApproximation
