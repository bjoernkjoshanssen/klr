module

public import Klr.UniformPartialBetting
public import Klr.EffectiveNormalization

/-!
# A uniformly computable family covering all strategy success sets

Every computable-real strategy has a success-preserving positive rational
capital approximation. Compiling its rational wagers into an ordinary action
program and using the two total simulators gives two members of one uniformly
primitive-recursive family covering its success on every input.

The family enumerates total simulators of arbitrary source codes; it does not
test which source programs are total or claim to enumerate all total functions.
-/

@[expose] public section

namespace Klr.UniformStrategyFamily

open RationalComputability

/-- Compile a positive rational strategy into the source scheduler's action
format. The canonical rational numerator and denominator encode its wager. -/
def action (π : ScanRule) (r : ReservedRationalCapital) (v : List Bool) :
    PartialBetting.Action :=
  (π.query v, (r.wager v).num, (r.wager v).den)

theorem computable_action (π : ScanRule) (r : ReservedRationalCapital) :
    Computable (action π r) :=
  π.computable_query.pair
    ((primrec_rat_num.to_comp.comp r.computable_wager).pair
      (primrec_rat_den.to_comp.comp r.computable_wager))

theorem fraction_action (π : ScanRule) (r : ReservedRationalCapital) (v : List Bool) :
    PartialBetting.fraction (action π r v) = r.wager v := by
  have h := PartialBetting.fraction_eq_of_legal (action π r v)
    (by simpa only [action, Rat.num_div_den] using (r.abs_wager_lt_one v).le)
  simpa only [action, Rat.num_div_den] using h

/-- One source code, fixed independently of the input, exactly reproduces the
positive rational capital along every actual scan transcript. -/
theorem exists_source_code (π : ScanRule) (r : ReservedRationalCapital) :
    ∃ c : Nat.Partrec.Code, ∀ X : Cantor, ∃ run : PartialBetting.SourceRun c X,
      ∀ n, PartialBetting.sourceCapital run n = r.value (π.transcript X n) := by
  obtain ⟨c, hc⟩ := PartialBetting.exists_partialAction _ (computable_action π r).partrec
  refine ⟨c, fun X => ?_⟩
  let a : ℕ → PartialBetting.Action := fun n => action π r (π.transcript X n)
  have hanswers (n : ℕ) :
      (PartialBetting.sourceAssignment a X n).map Prod.snd = π.transcript X n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [PartialBetting.sourceAssignment_succ, List.map_append, ih, π.transcript_succ]
      rfl
  let run : PartialBetting.SourceRun c X :=
    { action := a
      halts := fun n => (PartialBetting.approximate_complete c _ _).mp (by
        rw [hanswers, hc]
        exact Part.mem_some _)
      fresh := π.query_injective X }
  refine ⟨run, fun n => ?_⟩
  induction n with
  | zero => simp [PartialBetting.sourceCapital, r.initial]
  | succ n ih =>
    change (∏ i ∈ Finset.range (n + 1), PartialBetting.factor
      (PartialBetting.fraction (run.action i)) (X (run.action i).1)) = _
    rw [Finset.prod_range_succ]
    change PartialBetting.sourceCapital run n *
      PartialBetting.factor (PartialBetting.fraction (action π r (π.transcript X n)))
        (X (π.query (π.transcript X n))) = _
    rw [ih, fraction_action, π.transcript_succ, r.update]
    rfl

/-- Each original strategy's whole success set is covered by two total
simulators of one fixed rational source code. -/
theorem exists_code_cover (s : BettingStrategy) :
    ∃ c : Nat.Partrec.Code, ∀ X : Cantor, s.Succeeds X →
      (PartialBetting.strategy c false).Succeeds X ∨
      (PartialBetting.strategy c true).Succeeds X := by
  let q := CapitalApproximation.ofComputable s.capital s.computable_capital
  obtain ⟨c, hc⟩ := exists_source_code s.scan q.reserve
  refine ⟨c, fun X hX => ?_⟩
  obtain ⟨run, hrun⟩ := hc X
  have hsuccess := q.reserve_preserves_success s hX
  apply PartialBetting.two_total_strategies_cover run
  intro bound
  obtain ⟨n, hn⟩ := hsuccess bound
  exact ⟨n, by simpa only [hrun, ReservedRationalCapital.strategy,
    ReservedRationalCapital.capital] using hn⟩

/-- Decode a numerical index; malformed codes designate the zero program
on the even side. Every program/side pair has its ordinary encoded index. -/
def indexData (e : ℕ) : Nat.Partrec.Code × Bool :=
  (Encodable.decode e).getD (Nat.Partrec.Code.zero, false)

theorem primrec_indexData : Primrec indexData :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const (Nat.Partrec.Code.zero, false))

@[simp] theorem indexData_encode (p : Nat.Partrec.Code × Bool) :
    indexData (Encodable.encode p) = p := by simp [indexData]

/-- A genuine total betting strategy for every numerical index. -/
def strategy (e : ℕ) : BettingStrategy :=
  PartialBetting.strategy (indexData e).1 (indexData e).2

/-- The exact rational value of the indexed simulator's capital. -/
def value (e : ℕ) (v : List Bool) : ℚ :=
  PartialBetting.rationalCapital (indexData e).1 (indexData e).2 v

@[simp] theorem strategy_value (e : ℕ) (v : List Bool) :
    (strategy e).capital.value v = (value e v : ℝ) := rfl

theorem primrec_value : Primrec₂ value := by
  have h := PartialBetting.primrec_rationalCapital_uniform.comp
    ((primrec_indexData.comp Primrec.fst).pair Primrec.snd)
  exact h.of_eq (fun _ => rfl)

theorem primrec_query : Primrec (fun p : ℕ × List Bool =>
    (strategy p.1).scan.query p.2) := by
  have h := PartialBetting.primrec_scan_query_uniform.comp
    ((primrec_indexData.comp Primrec.fst).pair Primrec.snd)
  exact h.of_eq (fun _ => rfl)

section CanonicalApproximation

open _root_.Klr.Computability

local instance : Encodable ℚ := (inferInstance : Primcodable ℚ).toEncodable

/-- The ordinary approximation program chosen by the existing normalization
interface is uniformly computable in the second jump for this family. -/
theorem canonical_index_recursive :
    Nat.RecursiveIn {oracleFunction (OracleJump.zeroJump 2)} (fun i => Part.some
      (CanonicalCapitalApproximation.index (strategy i).capital.value
        (strategy i).computable_capital)) := by
  have h := CanonicalCapitalApproximation.index_recursive value primrec_value.to_comp
  exact h.of_eq (fun _ => rfl)

/-- The actual rational approximation used by `CapitalApproximation.ofComputable`
is uniformly second-jump computable, with numerical input coding the family
index and the transcript/precision pair. -/
theorem canonical_approximation_recursive :
    Nat.RecursiveIn {oracleFunction (OracleJump.zeroJump 2)} (fun z => Part.some
      (Encodable.encode ((CapitalApproximation.ofComputable
        (strategy (Nat.unpair z).1).capital (strategy (Nat.unpair z).1).computable_capital).value
          (CanonicalCapitalApproximation.input (Nat.unpair z).2).1
          (CanonicalCapitalApproximation.input (Nat.unpair z).2).2))) := by
  have h := CanonicalCapitalApproximation.value_recursive value primrec_value.to_comp
  exact h.of_eq (fun _ => rfl)

end CanonicalApproximation

/-- The family covers all successful original strategies, with two indices
chosen for each source strategy before the input is given. -/
theorem covers (s : BettingStrategy) :
    ∃ e₀ e₁ : ℕ, ∀ X : Cantor, s.Succeeds X →
      (strategy e₀).Succeeds X ∨ (strategy e₁).Succeeds X := by
  obtain ⟨c, hc⟩ := exists_code_cover s
  refine ⟨Encodable.encode (c, false), Encodable.encode (c, true), ?_⟩
  simpa only [strategy, indexData_encode] using hc

/-- Defeating this one effective family is exactly total-strategy KL
randomness in the repository's existing convention. -/
theorem kolmogorovLovelandRandom_iff (X : Cantor) :
    KolmogorovLovelandRandom X ↔ ∀ e, ¬ (strategy e).Succeeds X := by
  constructor
  · exact fun hX e => hX (strategy e)
  · intro hX s hs
    obtain ⟨e₀, e₁, h⟩ := covers s
    exact (h X hs).elim (hX e₀) (hX e₁)

/-- For any measure, it suffices to defeat every indexed simulator almost
surely. This effective family replaces a noneffective enumeration of strategies. -/
theorem ae_kolmogorovLovelandRandom_iff (μ : MeasureTheory.Measure Cantor) :
    (∀ᵐ X ∂μ, KolmogorovLovelandRandom X) ↔
      ∀ e, ∀ᵐ X ∂μ, ¬ (strategy e).Succeeds X := by
  simp only [kolmogorovLovelandRandom_iff]
  exact MeasureTheory.ae_all_iff

end Klr.UniformStrategyFamily
