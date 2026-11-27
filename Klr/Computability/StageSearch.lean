module

public import Klr.Computability.OracleRecursion
public import Klr.Computability.RelativeSearch

/-!
# Oracle search along valid construction histories

A bounded oracle-computable checker may offer several valid next histories,
and it need not offer any output on malformed histories. If a valid initial
history is given, successful outputs preserve validity, and some output exists
from every valid history, then the whole chosen run is computable in the same
oracle. This separates the effective search from its mathematical existence
proof and is the interface intended for the later affine stage construction.
-/

@[expose] public section

namespace Klr.Computability

/-- Iterate bounded witness search while maintaining an arbitrary semantic
invariant. The invariant itself need not be decidable in the oracle. -/
theorem exists_computable_stage_run {O : Set (ℕ →. ℕ)}
    {E : ℕ → ℕ → Option ℕ}
    (hE : Nat.RecursiveIn O (fun z => Part.some
      (Encodable.encode (E (Nat.unpair z).1 (Nat.unpair z).2))))
    {Valid : ℕ → Prop} {Step : ℕ → ℕ → Prop} {initial : ℕ}
    (hinitial : Valid initial)
    (hcomplete : ∀ s, Valid s → ∃ stage value, value ∈ E s stage)
    (hsound : ∀ s stage value, Valid s → value ∈ E s stage →
      Valid value ∧ Step s value) :
    ∃ run : ℕ → ℕ,
      Nat.RecursiveIn O (fun n => Part.some (run n)) ∧ run 0 = initial ∧
      (∀ n, Valid (run n)) ∧ ∀ n, Step (run n) (run (n + 1)) := by
  have hnext (s : ℕ) (hVs : Valid s) :
      ∃ t, t ∈ RelativeSearch.search E s ∧ Valid t := by
    have hd := (RelativeSearch.search_dom E s).mpr (hcomplete s hVs)
    obtain ⟨t, ht⟩ := Part.dom_iff_mem.mp hd
    obtain ⟨stage, hstage⟩ := RelativeSearch.search_spec ht
    exact ⟨t, ht, (hsound s stage t hVs hstage).1⟩
  obtain ⟨run, hrun, hzero, hvalid, hstep⟩ :=
    exists_computable_run (RelativeSearch.search_recursive hE) hinitial hnext
  refine ⟨run, hrun, hzero, hvalid, fun n => ?_⟩
  obtain ⟨stage, hstage⟩ := RelativeSearch.search_spec (hstep n)
  exact (hsound (run n) stage (run (n + 1)) (hvalid n) hstage).2

/-- The valid-history search theorem in Mathlib's total-computability notation. -/
theorem exists_computableIn_stage_run {A : Oracle}
    {E : ℕ → ℕ → Option ℕ}
    (hE : Nat.RecursiveIn {oracleFunction A} (fun z => Part.some
      (Encodable.encode (E (Nat.unpair z).1 (Nat.unpair z).2))))
    {Valid : ℕ → Prop} {Step : ℕ → ℕ → Prop} {initial : ℕ}
    (hinitial : Valid initial)
    (hcomplete : ∀ s, Valid s → ∃ stage value, value ∈ E s stage)
    (hsound : ∀ s stage value, Valid s → value ∈ E s stage →
      Valid value ∧ Step s value) :
    ∃ run : ℕ → ℕ, ComputableIn {oracleFunction A} run ∧ run 0 = initial ∧
      (∀ n, Valid (run n)) ∧ ∀ n, Step (run n) (run (n + 1)) := by
  obtain ⟨run, hrun, hzero, hvalid, hstep⟩ :=
    exists_computable_stage_run hE hinitial hcomplete hsound
  exact ⟨run, RecursiveIn.iff_nat.mpr hrun, hzero, hvalid, hstep⟩

end Klr.Computability
