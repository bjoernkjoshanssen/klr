module

public import Klr.Computability.Oracle

/-!
# Relative search for finite witnesses

A bounded enumerator may return different valid witnesses at different stages.
Searching for its first successful stage selects a witness using the same oracle.
The selected witness is not asserted to be the least witness of the underlying
semidecidable relation: the order is the order of the bounded enumeration.

`total_search` is the useful specialization in which all successful outputs agree
with a prescribed total function. The implementation uses Mathlib's actual
relative minimization operation, rather than a choice axiom for computability.

The encoded option operations and minimization argument are adapted from
`bjoernkjoshanssen/tt-auto`, commit
`3190d8d1a78e709297423d1343f68395127be5de`,
`OAI/Computability/DegreeRigidity/Effective/UniformOracle.lean` (Apache-2.0).
The general nonunique-witness selection interface is added here.
-/

@[expose] public section

namespace Klr.Computability

open Encodable

namespace RelativeSearch

/-- A bounded computation stage eventually returns an output on every input. -/
def Total (E : ℕ → ℕ → Option ℕ) : Prop :=
  ∀ n, ∃ stage value, value ∈ E n stage

theorem exists_success {E : ℕ → ℕ → Option ℕ} (hE : Total E) (n : ℕ) :
    ∃ stage, (E n stage).isSome = true := by
  obtain ⟨stage, value, hv⟩ := hE n
  exact ⟨stage, Option.isSome_iff_exists.mpr ⟨value, hv⟩⟩

/-- The least successful computation stage, not the least possible output. -/
def firstStage (E : ℕ → ℕ → Option ℕ) (hE : Total E) (n : ℕ) : ℕ :=
  Nat.find (exists_success hE n)

theorem firstStage_spec (E : ℕ → ℕ → Option ℕ) (hE : Total E) (n : ℕ) :
    (E n (firstStage E hE n)).isSome = true :=
  Nat.find_spec (exists_success hE n)

theorem before_firstStage {E : ℕ → ℕ → Option ℕ} (hE : Total E)
    {n stage : ℕ} (hstage : stage < firstStage E hE n) :
    (E n stage).isSome = false :=
  Bool.eq_false_iff.mpr (Nat.find_min (exists_success hE n) hstage)

/-- The output at the first successful stage. The default is never used. -/
def selected (E : ℕ → ℕ → Option ℕ) (hE : Total E) (n : ℕ) : ℕ :=
  (E n (firstStage E hE n)).getD 0

theorem selected_mem (E : ℕ → ℕ → Option ℕ) (hE : Total E) (n : ℕ) :
    selected E hE n ∈ E n (firstStage E hE n) := by
  obtain ⟨value, hv⟩ := Option.isSome_iff_exists.mp (firstStage_spec E hE n)
  have he : E n (firstStage E hE n) = some value := Option.mem_def.mp hv
  simp [selected, he]

/-- An encoded success test. Relative minimization searches for output zero. -/
def flag (code : ℕ) : ℕ :=
  if ((decode (α := Option ℕ) code).getD none).isSome then 0 else 1

/-- Recover the natural output of an encoded optional value. -/
def answer (code : ℕ) : ℕ :=
  ((decode (α := Option ℕ) code).getD none).getD 0

theorem flag_primrec : Primrec flag := by
  apply (Primrec.cond (Primrec.option_isSome.comp
    (Primrec.option_getD_default.comp (Primrec.decode (α := Option ℕ))))
    (Primrec.const 0) (Primrec.const 1)).of_eq
  intro n
  change (cond ((decode (α := Option ℕ) n).getD none).isSome 0 1) = _
  cases hh : ((decode (α := Option ℕ) n).getD none).isSome <;>
    simp only [flag, hh] <;> rfl

theorem answer_primrec : Primrec answer :=
  Primrec.option_getD_default.comp (Primrec.option_getD_default.comp Primrec.decode)

variable {O : Set (ℕ →. ℕ)} {E : ℕ → ℕ → Option ℕ}

/-- Partial search for a successful bounded stage. No totality is assumed. -/
def stageSearch (E : ℕ → ℕ → Option ℕ) (n : ℕ) : Part ℕ :=
  Nat.rfind fun stage => Part.some (E n stage).isSome

/-- Partial witness search, allowed to diverge on inputs with no witness. -/
def search (E : ℕ → ℕ → Option ℕ) (n : ℕ) : Part ℕ :=
  (stageSearch E n).map fun stage => (E n stage).getD 0

theorem stageSearch_recursive
    (hE : Nat.RecursiveIn O
      (fun z => Part.some (encode (E (Nat.unpair z).1 (Nat.unpair z).2)))) :
    Nat.RecursiveIn O (stageSearch E) := by
  have hflag := total_comp (total_primrec flag_primrec) hE
  apply (Nat.RecursiveIn.rfind hflag).of_eq
  intro n
  apply congrArg Nat.rfind
  funext stage
  simp only [Nat.unpair_pair]
  cases h : (E n stage).isSome <;> simp [flag, h]

/-- Bounded oracle enumeration supports partial search in the same oracle. -/
theorem search_recursive
    (hE : Nat.RecursiveIn O
      (fun z => Part.some (encode (E (Nat.unpair z).1 (Nat.unpair z).2)))) :
    Nat.RecursiveIn O (search E) := by
  have hp := Nat.RecursiveIn.pair (total_primrec Primrec.id) (stageSearch_recursive hE)
  have hr := Nat.RecursiveIn.comp (total_primrec answer_primrec)
    (Nat.RecursiveIn.comp hE hp)
  apply hr.of_eq
  intro n
  simp [search, Seq.seq, Part.bind_some_eq_map, answer, Part.map_map, Function.comp_def]

/-- Search terminates exactly when some bounded stage produces a witness. -/
theorem search_dom (E : ℕ → ℕ → Option ℕ) (n : ℕ) :
    (search E n).Dom ↔ ∃ stage value, value ∈ E n stage := by
  change (stageSearch E n).Dom ↔ _
  constructor
  · intro h
    obtain ⟨stage, hs, _⟩ := Nat.rfind_dom.mp h
    exact ⟨stage, Option.isSome_iff_exists.mp (Part.mem_some_iff.mp hs).symm⟩
  · rintro ⟨stage, value, hv⟩
    apply Nat.rfind_dom.mpr
    refine ⟨stage, ?_, fun {_} _ => trivial⟩
    exact Part.mem_some_iff.mpr (Option.isSome_iff_exists.mpr ⟨value, hv⟩).symm

/-- Every returned output occurs at a bounded computation stage. -/
theorem search_spec {E : ℕ → ℕ → Option ℕ} {n value : ℕ}
    (h : value ∈ search E n) : ∃ stage, value ∈ E n stage := by
  obtain ⟨stage, hs, hv⟩ := (Part.mem_map_iff _).mp h
  have hsome : (E n stage).isSome = true :=
    (Part.mem_some_iff.mp (Nat.rfind_spec hs)).symm
  obtain ⟨output, hout⟩ := Option.isSome_iff_exists.mp hsome
  have he : E n stage = some output := Option.mem_def.mp hout
  refine ⟨stage, ?_⟩
  simpa [he] using hv

/-- A semantic correctness predicate is preserved by partial witness search. -/
theorem search_sound {R : ℕ → ℕ → Prop}
    (hsound : ∀ n stage value, value ∈ E n stage → R n value)
    {n value : ℕ} (h : value ∈ search E n) : R n value := by
  obtain ⟨stage, hs⟩ := search_spec h
  exact hsound n stage value hs

/-- The first successful stage is recursive in the enumerator's oracle set. -/
theorem firstStage_recursive
    (hE : Nat.RecursiveIn O
      (fun z => Part.some (encode (E (Nat.unpair z).1 (Nat.unpair z).2))))
    (htotal : Total E) :
    Nat.RecursiveIn O (fun n => Part.some (firstStage E htotal n)) := by
  have hflag := total_comp (total_primrec flag_primrec) hE
  apply (Nat.RecursiveIn.rfind hflag).of_eq_tot
  intro n
  have hmem : firstStage E htotal n ∈ Nat.rfind (fun k =>
      (fun v : ℕ => decide (v = 0)) <$> Part.some (flag (encode (E n k)))) := by
    apply Nat.mem_rfind.mpr
    constructor
    · simp [flag, firstStage_spec E htotal n]
    · intro k hk
      simp [flag, before_firstStage htotal hk]
  simpa only [Nat.unpair_pair] using hmem

/-- Nonunique outputs can be selected without an additional jump. -/
theorem selected_recursive
    (hE : Nat.RecursiveIn O
      (fun z => Part.some (encode (E (Nat.unpair z).1 (Nat.unpair z).2))))
    (htotal : Total E) :
    Nat.RecursiveIn O (fun n => Part.some (selected E htotal n)) := by
  have hp := total_pair (total_primrec Primrec.id) (firstStage_recursive hE htotal)
  have hr := total_comp (total_primrec answer_primrec) (total_comp hE hp)
  exact hr.of_eq (fun n => by simp [selected, answer])

/-- A sound, eventually successful bounded enumerator has a recursive selector.
There is no agreement assumption on outputs from different stages. -/
theorem exists_selector {R : ℕ → ℕ → Prop}
    (hE : Nat.RecursiveIn O
      (fun z => Part.some (encode (E (Nat.unpair z).1 (Nat.unpair z).2))))
    (hsound : ∀ n stage value, value ∈ E n stage → R n value)
    (htotal : Total E) :
    ∃ f : ℕ → ℕ, Nat.RecursiveIn O (fun n => Part.some (f n)) ∧
      ∀ n, R n (f n) :=
  ⟨selected E htotal, selected_recursive hE htotal,
    fun n => hsound n _ _ (selected_mem E htotal n)⟩

/-- The same selector stated with Mathlib's total-function interface. -/
theorem exists_computableIn_selector {R : ℕ → ℕ → Prop}
    (hE : Nat.RecursiveIn O
      (fun z => Part.some (encode (E (Nat.unpair z).1 (Nat.unpair z).2))))
    (hsound : ∀ n stage value, value ∈ E n stage → R n value)
    (htotal : Total E) :
    ∃ f : ℕ → ℕ, ComputableIn O f ∧ ∀ n, R n (f n) := by
  obtain ⟨f, hf, hspec⟩ := exists_selector hE hsound htotal
  exact ⟨f, RecursiveIn.iff_nat.mpr hf, hspec⟩

end RelativeSearch

/-- If every successful enumerator output equals the specified total function,
that function is recursive in the same oracle set. -/
theorem total_search {O : Set (ℕ →. ℕ)} {E : ℕ → ℕ → Option ℕ}
    (hE : Nat.RecursiveIn O
      (fun z => Part.some (encode (E (Nat.unpair z).1 (Nat.unpair z).2))))
    (f : ℕ → ℕ) (hsound : ∀ n stage value, value ∈ E n stage → value = f n)
    (hcomplete : ∀ n, ∃ stage value, value ∈ E n stage) :
    Nat.RecursiveIn O (fun n => Part.some (f n)) := by
  have h := RelativeSearch.selected_recursive hE hcomplete
  exact h.of_eq (fun n => congrArg Part.some
    (hsound n _ _ (RelativeSearch.selected_mem E hcomplete n)))

end Klr.Computability
