module

public import Klr.SplittingClopen
public import Klr.Computability.RelativeComputable
public import Klr.Computability.ArithmeticSelection

/-!
# Selecting a path through almost-everywhere closed requirements

Finite restrictions retain a positive rational mass budget. A lower bound on
the mass of a closed restriction is a universal condition on the exact masses
of decreasing clopen approximants, so one jump decides it. The resulting
finite extension search and the infinite path use that same jump.
-/

@[expose] public section

namespace Klr.EffectiveClosedSelection

open MeasureTheory Filter _root_.Klr.Computability
  ArithmeticHierarchy RationalComputability
open scoped Topology

local instance : Encodable ℚ := (inferInstance : Primcodable ℚ).toEncodable

/-- Bounds and bits are stored with the newest pair first. -/
abbrev History := List (ℕ × Bool)

def word (h : History) : List Bool := h.reverse.map Prod.snd

@[simp] theorem word_nil : word [] = [] := rfl

@[simp] theorem word_cons (a : ℕ × Bool) (h : History) :
    word (a :: h) = word h ++ [a.2] := by simp [word]

@[simp] theorem length_word (h : History) : (word h).length = h.length := by simp [word]

theorem primrec_word : Primrec word :=
  Primrec.list_map Primrec.list_reverse (Primrec.snd.comp Primrec.snd).to₂

/-- The finite closed restriction attached to a history. -/
def region (C : ℕ → ℕ → Set Cantor) : History → Set Cantor
  | [] => Set.univ
  | a :: h => (region C h ∩ C h.length a.1) ∩ cylinder (word (a :: h))

@[simp] theorem region_nil (C : ℕ → ℕ → Set Cantor) : region C [] = Set.univ := rfl

theorem region_cons_subset (C : ℕ → ℕ → Set Cantor) (a : ℕ × Bool) (h : History) :
    region C (a :: h) ⊆ region C h := fun _ hx => hx.1.1

theorem region_subset_cylinder (C : ℕ → ℕ → Set Cantor) (h : History) :
    region C h ⊆ cylinder (word h) := by
  cases h with
  | nil => simp
  | cons a h => exact fun _ hx => hx.2

theorem isClosed_region {C : ℕ → ℕ → Set Cantor}
    (hC : ∀ e b, IsClosed (C e b)) (h : History) : IsClosed (region C h) := by
  induction h with
  | nil => exact isClosed_univ
  | cons a h ih => exact (ih.inter (hC _ _)).inter (isClosed_cylinder _)

def budget (n : ℕ) : ℚ := (1 / 4 : ℚ) ^ n

theorem budget_pos (n : ℕ) : 0 < budget n := pow_pos (by norm_num) _

@[simp] theorem budget_zero : budget 0 = 1 := by simp [budget]

theorem budget_succ (n : ℕ) : budget (n + 1) = budget n / 4 := by
  simp [budget, pow_succ, div_eq_mul_inv]

theorem primrec_budget : Primrec budget := by
  have h := primrec_rat_inv.comp (primrec_rat_natCast.comp
    ((Primrec₂.unpaired'.mp Nat.Primrec.pow).comp (Primrec.const 4) Primrec.id))
  exact h.of_eq fun _ => by simp [budget, one_div, inv_pow]

def Valid (μ : Measure Cantor) (C : ℕ → ℕ → Set Cantor) (h : History) : Prop :=
  (budget h.length : ℝ) ≤ μ.real (region C h)

theorem valid_nil (μ : Measure Cantor) [IsProbabilityMeasure μ]
    (C : ℕ → ℕ → Set Cantor) : Valid μ C [] := by simp [Valid]

theorem region_children_union (C : ℕ → ℕ → Set Cantor) (h : History) (b : ℕ) :
    region C ((b, false) :: h) ∪ region C ((b, true) :: h) =
      region C h ∩ C h.length b := by
  simp only [region, word_cons]
  rw [← Set.inter_union_distrib_left, Splitting.cylinder_children_union]
  exact Set.inter_eq_left.mpr (fun X hX => region_subset_cylinder C h hX.1)

/-- Every valid history has a valid one-bit extension meeting the next requirement. -/
theorem exists_valid_extension (μ : Measure Cantor) [IsProbabilityMeasure μ]
    (C : ℕ → ℕ → Set Cantor) (hC : ∀ e b, IsClosed (C e b))
    (hmono : ∀ e, Monotone (C e)) (hfull : ∀ e, μ (⋃ b, C e b) = 1)
    (h : History) (hh : Valid μ C h) : ∃ a : ℕ × Bool, Valid μ C (a :: h) := by
  have hmeas : MeasurableSet (⋃ b, C h.length b) :=
    MeasurableSet.iUnion (fun b => (hC _ b).measurableSet)
  have hae : ∀ᵐ X ∂μ, X ∈ ⋃ b, C h.length b :=
    (ae_iff_measure_eq hmeas.nullMeasurableSet).mpr (by
      change μ (⋃ b, C h.length b) = μ Set.univ
      simp [hfull])
  have he : (⋃ b, region C h ∩ C h.length b) = region C h ∩ ⋃ b, C h.length b := by
    ext X
    simp
  have hmass : μ (region C h ∩ ⋃ b, C h.length b) = μ (region C h) := by
    rw [Set.inter_comm]
    exact μ.measure_inter_eq_of_ae hae
  have ht : Tendsto (fun b => μ.real (region C h ∩ C h.length b)) atTop
      (𝓝 (μ.real (region C h))) := by
    have hm : Monotone (fun b => region C h ∩ C h.length b) :=
      fun i j hij => Set.inter_subset_inter_right _ (hmono _ hij)
    have ht := tendsto_measure_iUnion_atTop (μ := μ) hm
    rw [he, hmass] at ht
    exact (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp ht
  have hp : (0 : ℝ) < budget h.length := by exact_mod_cast budget_pos h.length
  have hlt : (budget h.length : ℝ) / 2 < μ.real (region C h) := by
    dsimp [Valid] at hh
    linarith
  obtain ⟨b, hb⟩ := (ht.eventually (eventually_gt_nhds hlt)).exists
  have hu := measureReal_union_le (μ := μ)
    (region C ((b, false) :: h)) (region C ((b, true) :: h))
  rw [region_children_union] at hu
  have hbudget : (budget (h.length + 1) : ℝ) = (budget h.length : ℝ) / 4 := by
    rw [budget_succ, Rat.cast_div, Rat.cast_ofNat]
  rcases le_total (budget (h.length + 1) : ℝ)
      (μ.real (region C ((b, false) :: h))) with hfalse | hfalse
  · exact ⟨(b, false), hfalse⟩
  · refine ⟨(b, true), ?_⟩
    change (budget (h.length + 1) : ℝ) ≤ _
    linarith

/-- Decreasing clopen approximants to every finite restriction, together with
their exact rational masses. Computability of `mass` is an explicit hypothesis
of the selection theorem below. -/
structure Approximation (μ : Measure Cantor) (C : ℕ → ℕ → Set Cantor) where
  event : History → ℕ → Set Cantor
  isClopen : ∀ h t, IsClopen (event h t)
  antitone : ∀ h, Antitone (event h)
  intersection : ∀ h, (⋂ t, event h t) = region C h
  mass : History → ℕ → ℚ
  mass_eq : ∀ h t, (mass h t : ℝ) = μ.real (event h t)

namespace Approximation

variable {μ : Measure Cantor} [IsProbabilityMeasure μ]
  {C : ℕ → ℕ → Set Cantor}

theorem valid_iff (D : Approximation μ C) (h : History) :
    Valid μ C h ↔ ∀ t, budget h.length ≤ D.mass h t := by
  constructor
  · intro hh t
    have hsub : region C h ⊆ D.event h t := by
      rw [← D.intersection h]
      exact Set.iInter_subset _ t
    have hm := (show (budget h.length : ℝ) ≤ μ.real (region C h) from hh).trans
      (measureReal_mono hsub)
    rw [← D.mass_eq h t] at hm
    exact_mod_cast hm
  · intro hh
    have ht := tendsto_measure_iInter_atTop
      (fun t => (D.isClopen h t).isClosed.measurableSet.nullMeasurableSet)
      (D.antitone h) (show ∃ t, μ (D.event h t) ≠ ⊤ from ⟨0, measure_ne_top _ _⟩)
    rw [D.intersection h] at ht
    apply le_of_tendsto_of_tendsto tendsto_const_nhds
      ((ENNReal.tendsto_toReal (measure_ne_top μ _)).comp ht)
    apply Eventually.of_forall
    intro t
    change (budget h.length : ℝ) ≤ μ.real (D.event h t)
    rw [← D.mass_eq]
    exact_mod_cast hh t

/-- The mass budget of a closed restriction is a uniform relative Π₁ predicate. -/
theorem valid_pi_one {A : Oracle} (D : Approximation μ C)
    (hm : ComputableIn₂ {oracleFunction A} D.mass) :
    Pi A 1 (fun n => Valid μ C (RelativeComputable.decodeDefault n)) := by
  classical
  have ht : ComputableIn {oracleFunction A} (fun p : History × ℕ =>
      decide (budget p.1.length ≤ D.mass p.1 p.2)) :=
    RelativeComputable.comp₂ (f := fun a b : ℚ => decide (a ≤ b))
      primrec_rat_le.decide.computableIn
      ((primrec_budget.comp (Primrec.list_length.comp Primrec.fst)).computableIn) hm
  have hi : Primrec (fun n : ℕ =>
      (RelativeComputable.decodeDefault (α := History) (Nat.unpair n).1,
        (Nat.unpair n).2)) :=
    (RelativeComputable.primrec_decodeDefault.comp (Primrec.fst.comp Primrec.unpair)).pair
      (Primrec.snd.comp Primrec.unpair)
  have hb := RelativeComputable.encode_recursive
    (RelativeComputable.comp bit_primrec.computableIn
      (RelativeComputable.comp ht hi.computableIn))
  have hmatrix : RecursivePred A (fun n =>
      budget (RelativeComputable.decodeDefault (α := History) (Nat.unpair n).1).length ≤
        D.mass (RelativeComputable.decodeDefault (Nat.unpair n).1) (Nat.unpair n).2) := by
    apply hb.of_eq
    intro n
    simp only [bit, decide_eq_true_eq, Encodable.encode_nat]
    split_ifs <;> rfl
  apply (forall_form (n := 0) hmatrix).congr
  intro n
  simpa only [Nat.unpair_pair] using (D.valid_iff (RelativeComputable.decodeDefault n)).symm

theorem valid_recursive_jump {A : Oracle} (D : Approximation μ C)
    (hm : ComputableIn₂ {oracleFunction A} D.mass) :
    RecursivePred (OracleJump.jump A)
      (fun n => Valid μ C (RelativeComputable.decodeDefault n)) :=
  OracleJump.form_recursive (D.valid_pi_one hm)

end Approximation

/-- An explicitly iterated finite-history transition. -/
def run (step : History → History) : ℕ → History
  | 0 => []
  | n + 1 => step (run step n)

theorem run_computableIn {O : Set (ℕ →. ℕ)} {step : History → History}
    (hs : ComputableIn O step) : ComputableIn O (run step) := by
  have hg : ComputableIn O (fun p : ℕ × (ℕ × History) => step p.2.2) :=
    RelativeComputable.comp hs
      (RelativeComputable.comp ComputableIn.snd ComputableIn.snd)
  have hr := RelativeComputable.nat_rec (g := fun _ _ h => step h)
    (ComputableIn.const ([] : History)) hg
  have h := RelativeComputable.comp hr
    (RelativeComputable.pair (ComputableIn.const 0) ComputableIn.id)
  apply RelativeComputable.of_eq h
  intro n
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg step ih

theorem run_length {step : History → History}
    (hstep : ∀ h, ∃ a, step h = a :: h) (n : ℕ) : (run step n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨a, ha⟩ := hstep (run step n)
    simp [run, ha, ih]

/-- A computable mass-preserving finite-history transition yields a computable
path meeting every closed requirement and every positive-mass prefix condition. -/
theorem exists_path_of_step {A : Oracle} (μ : Measure Cantor) [IsProbabilityMeasure μ]
    (C : ℕ → ℕ → Set Cantor) (hC : ∀ e b, IsClosed (C e b))
    (step : History → History) (hs : ComputableIn {oracleFunction A} step)
    (hstep : ∀ h, ∃ a, step h = a :: h)
    (hvalid : ∀ h, Valid μ C h → Valid μ C (step h)) :
    ∃ X : Cantor, ComputableIn {oracleFunction A} X ∧
      (∀ e, ∃ b, X ∈ C e b) ∧
      ∀ n, 0 < μ.real (cylinder (ScanRule.inputPrefix X n)) := by
  have hrun : ∀ n, Valid μ C (run step n) := by
    intro n
    induction n with
    | zero => exact valid_nil μ C
    | succ n ih => exact hvalid _ ih
  have hnest : ∀ n, region C (run step (n + 1)) ⊆ region C (run step n) := by
    intro n
    obtain ⟨a, ha⟩ := hstep (run step n)
    rw [run, ha]
    exact region_cons_subset C a _
  have hpositive (n : ℕ) : 0 < μ.real (region C (run step n)) :=
    (show (0 : ℝ) < budget (run step n).length by
      exact_mod_cast budget_pos (run step n).length).trans_le (hrun n)
  have hnonempty (n : ℕ) : (region C (run step n)).Nonempty := by
    apply nonempty_of_measure_ne_zero (μ := μ)
    intro hz
    have hp := hpositive n
    simp [measureReal_def, hz] at hp
  obtain ⟨X, hX⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => region C (run step n)) hnest hnonempty
    (isClosed_region hC _).isCompact (fun n => isClosed_region hC _)
  have hmem (n : ℕ) : X ∈ region C (run step n) := Set.mem_iInter.mp hX n
  have hpref (n : ℕ) : ScanRule.inputPrefix X n = word (run step n) :=
    (PoolAdvice.inputPrefix_eq_iff_mem_cylinder X n _
      (by simp [run_length hstep])).mpr (region_subset_cylinder C _ (hmem n))
  have hc : ComputableIn {oracleFunction A}
      (fun n => (word (run step (n + 1))).getD n false) :=
    RelativeComputable.comp₂ (f := fun (l : List Bool) n => l.getD n false)
      (Primrec.list_getD false).computableIn₂
      (RelativeComputable.comp primrec_word.computableIn
        (RelativeComputable.comp (run_computableIn hs) ComputableIn.succ)) ComputableIn.id
  refine ⟨X, RelativeComputable.of_eq hc (fun n => ?_), ?_, ?_⟩
  · rw [← hpref (n + 1)]
    exact ScanRule.getD_inputPrefix X (Nat.lt_succ_self n)
  · intro e
    obtain ⟨a, ha⟩ := hstep (run step e)
    have hm := hmem (e + 1)
    rw [run, ha] at hm
    exact ⟨a.1, by simpa only [run_length hstep] using hm.1.2⟩
  · intro n
    rw [hpref]
    exact (hpositive n).trans_le (measureReal_mono (region_subset_cylinder C _))

private def extensionCode (n : ℕ) : ℕ :=
  Encodable.encode
    (RelativeComputable.decodeDefault (α := ℕ × Bool) (Nat.unpair n).2 ::
      RelativeComputable.decodeDefault (α := History) (Nat.unpair n).1)

private theorem primrec_extensionCode : Primrec extensionCode :=
  Primrec.encode.comp (Primrec.list_cons.comp
    (RelativeComputable.primrec_decodeDefault.comp (Primrec.snd.comp Primrec.unpair))
    (RelativeComputable.primrec_decodeDefault.comp (Primrec.fst.comp Primrec.unpair)))

/-- One jump suffices to choose a path meeting all the almost-everywhere closed
requirements, while keeping every prefix in the support of the measure. -/
theorem exists_path {A : Oracle} (μ : Measure Cantor) [IsProbabilityMeasure μ]
    (C : ℕ → ℕ → Set Cantor) (hC : ∀ e b, IsClosed (C e b))
    (hmono : ∀ e, Monotone (C e)) (hfull : ∀ e, μ (⋃ b, C e b) = 1)
    (D : Approximation μ C) (hm : ComputableIn₂ {oracleFunction A} D.mass) :
    ∃ X : Cantor, ComputableIn {oracleFunction (OracleJump.jump A)} X ∧
      (∀ e, ∃ b, X ∈ C e b) ∧
      ∀ n, 0 < μ.real (cylinder (ScanRule.inputPrefix X n)) := by
  let P : ℕ → Prop := fun n =>
    ¬ Valid μ C (RelativeComputable.decodeDefault (Nat.unpair n).1) ∨
      Valid μ C
        (RelativeComputable.decodeDefault (α := ℕ × Bool) (Nat.unpair n).2 ::
          RelativeComputable.decodeDefault (Nat.unpair n).1)
  have hv := D.valid_recursive_jump hm
  have hp : RecursivePred (OracleJump.jump A) P := by
    have hl := recursive_not (recursive_comp hv (Primrec.fst.comp Primrec.unpair))
    have hr := recursive_comp hv primrec_extensionCode
    apply (Form.or (n := 0) (s := true) hl hr).congr
    intro n
    simp only [P, extensionCode, RelativeComputable.decodeDefault_encode]
  have htotal : ∀ n, ∃ a, P (Nat.pair n a) := by
    intro n
    by_cases hh : Valid μ C (RelativeComputable.decodeDefault n)
    · obtain ⟨a, ha⟩ := exists_valid_extension μ C hC hmono hfull _ hh
      exact ⟨Encodable.encode a, by simpa [P] using Or.inr ha⟩
    · exact ⟨0, by simp [P, hh]⟩
  let select : ℕ → ℕ := ArithmeticSelection.least P htotal
  have hselect : ComputableIn {oracleFunction (OracleJump.jump A)} select :=
    RecursiveIn.iff_nat.mpr (ArithmeticSelection.least_recursive hp htotal)
  let step : History → History := fun h =>
    RelativeComputable.decodeDefault (select (Encodable.encode h)) :: h
  have hs : ComputableIn {oracleFunction (OracleJump.jump A)} step :=
    RelativeComputable.comp₂ (f := fun a h => a :: h) Primrec.list_cons.computableIn₂
      (RelativeComputable.comp RelativeComputable.primrec_decodeDefault.computableIn
        (RelativeComputable.comp hselect Primrec.encode.computableIn)) ComputableIn.id
  apply exists_path_of_step μ C hC step hs
  · intro h
    exact ⟨_, rfl⟩
  · intro h hh
    have he := ArithmeticSelection.least_spec P htotal (Encodable.encode h)
    have he' : ¬ Valid μ C h ∨ Valid μ C (step h) := by
      simpa only [P, Nat.unpair_pair, RelativeComputable.decodeDefault_encode] using he
    exact he'.resolve_left (fun hn => hn hh)

/-- The conclusion also has the direct Turing-reducibility formulation. -/
theorem exists_path_reduces {A : Oracle} (μ : Measure Cantor) [IsProbabilityMeasure μ]
    (C : ℕ → ℕ → Set Cantor) (hC : ∀ e b, IsClosed (C e b))
    (hmono : ∀ e, Monotone (C e)) (hfull : ∀ e, μ (⋃ b, C e b) = 1)
    (D : Approximation μ C) (hm : ComputableIn₂ {oracleFunction A} D.mass) :
    ∃ X : Cantor, Reduces X (OracleJump.jump A) ∧
      (∀ e, ∃ b, X ∈ C e b) ∧
      ∀ n, 0 < μ.real (cylinder (ScanRule.inputPrefix X n)) := by
  obtain ⟨X, hX, hC, hp⟩ := exists_path μ C hC hmono hfull D hm
  refine ⟨X, ?_, hC, hp⟩
  exact RelativeComputable.comp bit_primrec.computableIn hX

/-- Positive mass for every prefix forces membership in every closed set of
full measure. In particular this applies to every affine block event. -/
theorem mem_closed_of_positive_prefixes (μ : Measure Cantor) [IsProbabilityMeasure μ]
    (X : Cantor) (hp : ∀ n, 0 < μ.real (cylinder (ScanRule.inputPrefix X n)))
    {F : Set Cantor} (hF : IsClosed F) (hfull : μ F = 1) : X ∈ F := by
  have hae : ∀ᵐ Y ∂μ, Y ∈ F :=
    (ae_iff_measure_eq hF.measurableSet.nullMeasurableSet).mpr (by
      change μ F = μ Set.univ
      simpa using hfull)
  have hn : ∀ n, (F ∩ cylinder (ScanRule.inputPrefix X n)).Nonempty := by
    intro n
    apply nonempty_of_measure_ne_zero (μ := μ)
    rw [μ.measure_inter_eq_of_ae hae]
    intro hz
    have hp' := hp n
    simp [measureReal_def, hz] at hp'
  choose Y hY using hn
  have hlim : Tendsto Y atTop (𝓝 X) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop i] with n hn
    exact (((hY n).2 i (by simpa using hn)).trans (ScanRule.getD_inputPrefix X hn)).symm
  exact hF.mem_of_tendsto hlim (Eventually.of_forall fun n => (hY n).1)

end Klr.EffectiveClosedSelection
