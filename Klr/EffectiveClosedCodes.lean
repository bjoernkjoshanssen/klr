module

public import Klr.EffectiveClosedSelection
public import Klr.RationalPrefixCode

/-!
# Closed-class selection from coded clopens and exact cylinder masses

The oracle hypothesis is an actual relative computation of rational cylinder
masses. Exact masses of coded clopen sets are finite sums of those values.
Thus a uniformly computable decreasing family of clopen codes supplies all
the mass tests needed by the one-jump closed-class selection theorem.
-/

@[expose] public section

namespace Klr.EffectiveClosedCodes

open MeasureTheory RationalComputability SparseSearch
  _root_.Klr.Computability EffectiveClosedSelection
open scoped BigOperators

local instance : Encodable ℚ := (inferInstance : Primcodable ℚ).toEncodable

/-- Bounded rational summation preserves the oracle. -/
theorem computableIn_boundedSum {α : Type*} [Primcodable α] [Inhabited α]
    {O : Set (ℕ →. ℕ)} {f : α → ℕ → ℚ} (hf : ComputableIn₂ O f) :
    ComputableIn O (fun p : α × ℕ => PoolAdvice.boundedSum (f p.1) p.2) := by
  have hv : ComputableIn O (fun p : α × (ℕ × ℚ) => f p.1 p.2.1) :=
    RelativeComputable.comp₂ hf ComputableIn.fst
      (RelativeComputable.comp ComputableIn.fst ComputableIn.snd)
  have hs : ComputableIn O (fun p : α × (ℕ × ℚ) => p.2.2 + f p.1 p.2.1) :=
    RelativeComputable.comp₂ (f := fun a b : ℚ => a + b) primrec_rat_add.computableIn₂
      (RelativeComputable.comp ComputableIn.snd ComputableIn.snd) hv
  have hr := RelativeComputable.nat_rec (g := fun a n v => v + f a n)
    (ComputableIn.const (0 : ℚ)) hs
  apply RelativeComputable.of_eq hr
  intro p
  induction p.2 with
  | zero => rfl
  | succ n ih => exact congrArg (fun v => v + f p.1 n) ih

/-- Summing oracle-computable terms over an oracle-computable finite list. -/
theorem computableIn_list_sum {α β : Type*} [Primcodable α] [Primcodable β]
    [Inhabited α] [Inhabited β] {O : Set (ℕ →. ℕ)}
    {l : α → List β} {f : α → β → ℚ}
    (hl : ComputableIn O l) (hf : ComputableIn₂ O f) :
    ComputableIn O (fun a => ((l a).map (f a)).sum) := by
  have hg : ComputableIn O (fun p : α × ℕ => (l p.1).getD p.2 default) :=
    RelativeComputable.comp₂ (f := fun (w : List β) n => w.getD n default)
      (Primrec.list_getD default).computableIn₂
      (RelativeComputable.comp hl ComputableIn.fst) ComputableIn.snd
  have hv : ComputableIn₂ O (fun a n => f a ((l a).getD n default)) :=
    RelativeComputable.comp₂ hf ComputableIn.fst hg
  have hs := RelativeComputable.comp (computableIn_boundedSum hv)
    (RelativeComputable.pair ComputableIn.id
      (RelativeComputable.comp Primrec.list_length.computableIn hl))
  exact RelativeComputable.of_eq hs fun a => PoolAdvice.boundedSum_getD (f a) (l a) default

/-- Exact probability of a finite clopen code from exact cylinder probabilities. -/
def codeMass (q : List Bool → ℚ) (c : RationalPrefixCode.Code) : ℚ :=
  ((words c.1).map (fun s => if (1 / 2 : ℚ) < RationalPrefixCode.value c s then q s else 0)).sum

theorem codeMass_computableIn {O : Set (ℕ →. ℕ)} {q : List Bool → ℚ}
    (hq : ComputableIn O q) : ComputableIn O (codeMass q) := by
  have hb : Computable (fun p : RationalPrefixCode.Code × List Bool =>
      decide ((1 / 2 : ℚ) < RationalPrefixCode.value p.1 p.2)) :=
    PoolAdvice.computable_rat_lt.comp (Computable.const (1 / 2))
      RationalPrefixCode.primrec_value.to_comp
  have hi : ComputableIn O (fun p : RationalPrefixCode.Code × List Bool =>
      (decide ((1 / 2 : ℚ) < RationalPrefixCode.value p.1 p.2), (q p.2, (0 : ℚ)))) :=
    RelativeComputable.pair hb.computableIn
      (RelativeComputable.pair (RelativeComputable.comp hq ComputableIn.snd)
        (ComputableIn.const 0))
  have hcond : Primrec (fun p : Bool × (ℚ × ℚ) => _root_.cond p.1 p.2.1 p.2.2) :=
    Primrec.cond Primrec.fst (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hf : ComputableIn₂ O (fun c s =>
      if (1 / 2 : ℚ) < RationalPrefixCode.value c s then q s else 0) :=
    RelativeComputable.of_eq (RelativeComputable.comp hcond.computableIn hi) fun _ => by simp
  exact computableIn_list_sum
    (RelativeComputable.comp computable_words.computableIn ComputableIn.fst) hf

theorem codeMass_eq (μ : Measure Cantor) [IsFiniteMeasure μ]
    (q : List Bool → ℚ) (hq : ∀ s, (q s : ℝ) = μ.real (cylinder s))
    (c : RationalPrefixCode.Code) :
    (codeMass q c : ℝ) = μ.real (RationalPrefixCode.event c) := by
  classical
  let f : List Bool → ℝ := fun s =>
    if (1 / 2 : ℚ) < RationalPrefixCode.value c s then 1 else 0
  have hi : (RationalPrefixCode.event c).indicator (fun _ => (1 : ℝ)) =
      fun X => f (ScanRule.inputPrefix X c.1) := by
    funext X
    simp only [f, RationalPrefixCode.event, RationalPrefixCode.eval, Set.indicator_apply,
      Set.mem_ofPred_eq]
  have hi' : (∫ X, f (ScanRule.inputPrefix X c.1) ∂μ) =
      μ.real (RationalPrefixCode.event c) := by
    rw [← hi]
    exact integral_indicator_one (RationalPrefixCode.measurableSet_event c)
  rw [← hi', PoolAdvice.prefixFunction_eq_sum,
    integral_finsetSum _ (fun s _ =>
      (integrable_const (f s)).indicator (measurableSet_cylinder s))]
  rw [codeMass, Rat.cast_list_sum, List.map_map,
    List.sum_toFinset _ (PoolAdvice.nodup_words c.1)]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s hs
  rw [integral_indicator_const _ (measurableSet_cylinder s)]
  by_cases hp : (1 / 2 : ℚ) < RationalPrefixCode.value c s <;>
    simp only [f, Function.comp_apply, hp, ite_true, ite_false, Rat.cast_zero, hq,
      smul_eq_mul, mul_one, mul_zero]

/-- Package coded clopen approximants as the mass approximation used by the
closed-selection theorem. -/
def approximation (μ : Measure Cantor) [IsProbabilityMeasure μ]
    (C : ℕ → ℕ → Set Cantor) (q : List Bool → ℚ)
    (hq : ∀ s, (q s : ℝ) = μ.real (cylinder s))
    (d : History → ℕ → RationalPrefixCode.Code)
    (hanti : ∀ h, Antitone (fun t => RationalPrefixCode.event (d h t)))
    (hinter : ∀ h, (⋂ t, RationalPrefixCode.event (d h t)) = region C h) :
    Approximation μ C where
  event h t := RationalPrefixCode.event (d h t)
  isClopen h t := RationalPrefixCode.isClopen_event (d h t)
  antitone := hanti
  intersection := hinter
  mass h t := codeMass q (d h t)
  mass_eq h t := codeMass_eq μ q hq (d h t)

/-- The one-jump path theorem with only finite-code and cylinder-mass
computability hypotheses. -/
theorem exists_path {A : Oracle} (μ : Measure Cantor) [IsProbabilityMeasure μ]
    (C : ℕ → ℕ → Set Cantor) (hC : ∀ e b, IsClosed (C e b))
    (hmono : ∀ e, Monotone (C e)) (hfull : ∀ e, μ (⋃ b, C e b) = 1)
    (q : List Bool → ℚ) (hqcomp : ComputableIn {oracleFunction A} q)
    (hq : ∀ s, (q s : ℝ) = μ.real (cylinder s))
    (d : History → ℕ → RationalPrefixCode.Code)
    (hd : ComputableIn₂ {oracleFunction A} d)
    (hanti : ∀ h, Antitone (fun t => RationalPrefixCode.event (d h t)))
    (hinter : ∀ h, (⋂ t, RationalPrefixCode.event (d h t)) = region C h) :
    ∃ X : Cantor, Reduces X (OracleJump.jump A) ∧
      (∀ e, ∃ b, X ∈ C e b) ∧
      ∀ n, 0 < μ.real (cylinder (ScanRule.inputPrefix X n)) :=
  EffectiveClosedSelection.exists_path_reduces μ C hC hmono hfull
    (approximation μ C q hq d hanti hinter)
    (RelativeComputable.comp (f := codeMass q) (codeMass_computableIn hqcomp) hd)

end Klr.EffectiveClosedCodes
