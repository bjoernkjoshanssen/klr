module

public import Klr.CoordinateRefinement
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Simultaneous coordinate selection in the second jump

Iterating finite reservoir refinements produces increasing positions and
simultaneously convergent coordinates. The rational interval chosen at the
known stage `Nat.pair i k` gives a uniform second-jump name for the `i`th
limit. Every sufficiently late position remains in each earlier reservoir;
those reservoirs provide local upper bounds arbitrarily close to each limit.
-/

@[expose] public section

namespace Klr.CoordinateSelection

open Filter Encodable Klr.Computability Klr.Computability.OracleJump
open Klr.LeftCeReservoir Klr.CoordinateRefinement
open scoped Topology

local instance : Encodable ℚ := (inferInstance : Primcodable ℚ).toEncodable

/-- A numerical run of the actual second-jump refinement procedure. -/
structure Run (f : ℕ → ℕ → ℝ) where
  code : ℕ → ℕ
  choose : ℕ → ℕ
  code_recursive : Nat.RecursiveIn {oracleFunction (zeroJump 2)}
    (fun n => Part.some (code n))
  choose_recursive : Nat.RecursiveIn {oracleFunction (zeroJump 2)}
    (fun n => Part.some (choose n))
  zero : code 0 = encode ((0, (0, [])) : State)
  succ : ∀ n, code (n + 1) = nextCode (code n) (choose (code n))
  good : ∀ n, Good f (readState (code n)) (readCandidate (choose (code n)))

/-- The proved selector and ordinary primitive iteration produce such a run. -/
theorem exists_run {f : ℕ → ℕ → ℝ} (D : LowerName f)
    (hf0 : ∀ i n, 0 ≤ f i n) (hf1 : ∀ i n, f i n ≤ 1) : Nonempty (Run f) := by
  obtain ⟨choose, hchoose, hgood⟩ := CoordinateRefinement.exists_selector D hf0 hf1
  let step : ℕ → ℕ := fun v => nextCode v (choose v)
  have hnext : Primrec (fun z : ℕ => nextCode (Nat.unpair z).1 (Nat.unpair z).2) :=
    nextCode_primrec.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)
  have hstep := total_comp (total_primrec hnext)
    (total_pair (total_primrec Primrec.id) hchoose)
  have hstep' : Nat.RecursiveIn {oracleFunction (zeroJump 2)}
      (fun v => Part.some (step v)) := by simpa only [Nat.unpair_pair, id_eq] using hstep
  let initial : ℕ := encode ((0, (0, [])) : State)
  let run : ℕ → ℕ := fun n => step^[n] initial
  have hrun : Nat.RecursiveIn {oracleFunction (zeroJump 2)}
      (fun n => Part.some (run n)) := total_iterate hstep' initial
  have hzero : run 0 = initial := rfl
  have hsucc (n : ℕ) : run (n + 1) = nextCode (run n) (choose (run n)) := by
    exact Function.iterate_succ_apply' step n initial
  have hvalid : ∀ n, Valid f (run n) := by
    intro n
    induction n with
    | zero =>
      change Unbounded f (readState initial).2
      simp only [initial, readState_encode]
      intro b
      exact ⟨b, le_rfl, by simp [Contains]⟩
    | succ n ih =>
      have hg := hgood (run n) ih
      rw [hsucc]
      simpa only [Valid, nextCode, readState_encode, advance] using hg.2.1
  exact ⟨⟨run, choose, hrun, hchoose, hzero, hsucc, fun n => hgood (run n) (hvalid n)⟩⟩

namespace Run

variable {f : ℕ → ℕ → ℝ} (R : Run f)

def state (n : ℕ) : State := readState (R.code n)
def witness (n : ℕ) : Candidate := readCandidate (R.choose (R.code n))
def reservoir (n : ℕ) : Reservoir := (R.state n).2
def position (n : ℕ) : ℕ := (R.reservoir n).1

@[simp] theorem state_zero : R.state 0 = (0, (0, [])) := by
  change readState (R.code 0) = (0, (0, []))
  rw [R.zero, readState_encode]

theorem state_succ (n : ℕ) : R.state (n + 1) = advance (R.state n) (R.witness n) := by
  simp only [state, R.succ, nextCode, readState_encode, witness]

theorem state_index (n : ℕ) : (R.state n).1 = n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [R.state_succ, advance, ih]

theorem good_witness (n : ℕ) : Good f (R.state n) (R.witness n) := R.good n

theorem reservoir_succ (n : ℕ) :
    R.reservoir (n + 1) = cut (R.reservoir n) (Nat.unpair n).1
      (R.witness n).1 (R.witness n).2.2 := by
  simp only [reservoir, R.state_succ, advance, lower, R.state_index]

theorem position_succ (n : ℕ) : R.position (n + 1) = (R.witness n).2.2 := by
  have h := (R.good_witness n).1.1
  change (R.reservoir n).1 < (R.witness n).2.2 at h
  simp only [position, R.reservoir_succ, cut]
  exact max_eq_right h.le

theorem position_strictMono : StrictMono R.position := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [R.position_succ]
  exact (R.good_witness n).1.1

theorem position_mem (n : ℕ) : Contains f (R.reservoir n) (R.position n) := by
  cases n with
  | zero => simp [reservoir, position, R.state_zero, Contains]
  | succ n =>
    rw [R.position_succ]
    change Contains f (R.state (n + 1)).2 (R.witness n).2.2
    rw [R.state_succ]
    exact (R.good_witness n).2.2.2

/-- Every later reservoir is contained in every earlier one. -/
theorem contains_of_le {n m b : ℕ} (hnm : n ≤ m)
    (hb : Contains f (R.reservoir m) b) : Contains f (R.reservoir n) b := by
  induction m, hnm using Nat.le_induction with
  | base => exact hb
  | succ m hnm ih =>
    rw [R.reservoir_succ] at hb
    exact ih (contains_cut.mp hb).1

/-- All selected positions eventually lie in any fixed earlier reservoir. -/
theorem eventually_mem (n : ℕ) : ∀ᶠ m in atTop, Contains f (R.reservoir n) (R.position m) := by
  filter_upwards [eventually_ge_atTop n] with m hm
  exact R.contains_of_le hm (R.position_mem m)

theorem position_recursive : Nat.RecursiveIn {oracleFunction (zeroJump 2)}
    (fun n => Part.some (R.position n)) := by
  change Nat.RecursiveIn {oracleFunction (zeroJump 2)}
    (fun n => Part.some (readState (R.code n)).2.1)
  exact total_comp (total_primrec (Primrec.fst.comp (Primrec.snd.comp readState_primrec)))
    R.code_recursive

theorem position_computableIn : ComputableIn {oracleFunction (zeroJump 2)} R.position :=
  RecursiveIn.iff_nat.mpr R.position_recursive

/-- The finite reservoir data, as well as its cutoff, is uniformly computable. -/
theorem reservoir_code_recursive : Nat.RecursiveIn {oracleFunction (zeroJump 2)}
    (fun n => Part.some (encode (R.reservoir n))) := by
  change Nat.RecursiveIn {oracleFunction (zeroJump 2)}
    (fun n => Part.some (encode (readState (R.code n)).2))
  exact total_comp (total_primrec
    (Primrec.encode.comp (Primrec.snd.comp readState_primrec))) R.code_recursive

theorem reservoir_computableIn :
    ComputableIn {oracleFunction (zeroJump 2)} R.reservoir := by
  simpa [ComputableIn, RecursiveIn] using R.reservoir_code_recursive

/-- Every member of the next reservoir obeys its chosen interval. -/
theorem reservoir_interval (n b : ℕ) (hb : Contains f (R.reservoir (n + 1)) b) :
    ((R.witness n).1 : ℝ) < f (Nat.unpair n).1 b ∧
      f (Nat.unpair n).1 b ≤ ((R.witness n).2.1 : ℝ) := by
  rw [R.reservoir_succ] at hb
  obtain ⟨hOld, hN, hl⟩ := contains_cut.mp hb
  refine ⟨hl, ?_⟩
  by_contra h
  have hu : ((R.witness n).2.1 : ℝ) < f (Nat.unpair n).1 b := lt_of_not_ge h
  apply (R.good_witness n).2.2.1 b
  change Contains f (cut (R.reservoir n) (Nat.unpair (R.state n).1).1
    (R.witness n).2.1 (R.witness n).2.2) b
  rw [R.state_index]
  exact contains_cut.mpr ⟨hOld, hN, hu⟩

theorem position_interval (i k m : ℕ) (hm : Nat.pair i k + 1 ≤ m) :
    ((R.witness (Nat.pair i k)).1 : ℝ) < f i (R.position m) ∧
      f i (R.position m) ≤ ((R.witness (Nat.pair i k)).2.1 : ℝ) := by
  simpa only [Nat.unpair_pair] using R.reservoir_interval (Nat.pair i k) (R.position m)
    (R.contains_of_le hm (R.position_mem m))

theorem interval_width (i k : ℕ) :
    ((R.witness (Nat.pair i k)).2.1 : ℝ) - (R.witness (Nat.pair i k)).1 <
      (1 / 2 : ℝ) ^ k := by
  have h := (R.good_witness (Nat.pair i k)).1.2.2
  rw [R.state_index, Nat.unpair_pair] at h
  simp only [CauchyModulus.dyadic] at h
  have hr := (Rat.cast_lt (K := ℝ)).mpr h
  push_cast at hr
  exact hr

/-- Shrinking interval constraints make every coordinate sequence Cauchy. -/
theorem coordinate_cauchy (i : ℕ) : CauchySeq (fun n => f i (R.position n)) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  refine ⟨Nat.pair i k + 1, fun m hm n hn => ?_⟩
  have hm' := R.position_interval i k m hm
  have hn' := R.position_interval i k n hn
  have hw := R.interval_width i k
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- The simultaneous coordinate limits, with their numerical names below. -/
noncomputable def limit (i : ℕ) : ℝ :=
  Classical.choose (cauchySeq_tendsto_of_complete (R.coordinate_cauchy i))

theorem coordinate_tendsto (i : ℕ) :
    Tendsto (fun n => f i (R.position n)) atTop (𝓝 (R.limit i)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete (R.coordinate_cauchy i))

theorem limit_interval (i k : ℕ) :
    ((R.witness (Nat.pair i k)).1 : ℝ) ≤ R.limit i ∧
      R.limit i ≤ ((R.witness (Nat.pair i k)).2.1 : ℝ) := by
  have hev : ∀ᶠ m in atTop,
      ((R.witness (Nat.pair i k)).1 : ℝ) ≤ f i (R.position m) ∧
        f i (R.position m) ≤ ((R.witness (Nat.pair i k)).2.1 : ℝ) := by
    filter_upwards [eventually_ge_atTop (Nat.pair i k + 1)] with m hm
    exact ⟨(R.position_interval i k m hm).1.le, (R.position_interval i k m hm).2⟩
  exact ⟨ge_of_tendsto (R.coordinate_tendsto i) (hev.mono fun _ h => h.1),
    le_of_tendsto (R.coordinate_tendsto i) (hev.mono fun _ h => h.2)⟩

/-- A rational name read directly from the scheduled refinement witness. -/
def approximation (i k : ℕ) : ℚ := (R.witness (Nat.pair i k)).1

theorem approximation_error (i k : ℕ) :
    ‖(R.approximation i k : ℝ) - R.limit i‖ ≤ (1 / 2 : ℝ) ^ k := by
  have hl := (R.limit_interval i k).1
  have hu := (R.limit_interval i k).2
  have hw := R.interval_width i k
  rw [approximation, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hl)]
  linarith

/-- The cylinder-coordinate names are uniformly second-jump computable. -/
theorem approximation_computableIn :
    ComputableIn₂ {oracleFunction (zeroJump 2)} R.approximation := by
  have hchoice := total_comp R.choose_recursive R.code_recursive
  have hval := total_comp (total_primrec
    (Primrec.encode.comp (Primrec.fst.comp readCandidate_primrec))) hchoice
  simpa [ComputableIn₂, ComputableIn, RecursiveIn, Encodable.decode_prod_val,
    approximation, witness, Nat.pair_unpair] using hval

/-- Each selected finite reservoir has its original ordinary c.e. membership test. -/
theorem reservoir_re (D : LowerName f) (n : ℕ) : REPred (Contains f (R.reservoir n)) :=
  D.contains_re _

/-- Arbitrarily close local upper bounds hold on c.e. reservoirs containing
all sufficiently late selected positions. -/
theorem exists_reservoir (D : LowerName f) (i : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Set ℕ, REPred (fun b => b ∈ S) ∧ (∀ᶠ n in atTop, R.position n ∈ S) ∧
      ∀ b ∈ S, f i b ≤ R.limit i + ε := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  refine ⟨{b | Contains f (R.reservoir (Nat.pair i k + 1)) b},
    R.reservoir_re D _, R.eventually_mem _, ?_⟩
  intro b hb
  have hu := (R.reservoir_interval (Nat.pair i k) b hb).2
  simp only [Nat.unpair_pair] at hu
  have hl := (R.limit_interval i k).1
  have hw := R.interval_width i k
  linarith

theorem limit_nonneg (hf0 : ∀ i n, 0 ≤ f i n) (i : ℕ) : 0 ≤ R.limit i :=
  ge_of_tendsto' (R.coordinate_tendsto i) (fun n => hf0 i (R.position n))

theorem limit_le_one (hf1 : ∀ i n, f i n ≤ 1) (i : ℕ) : R.limit i ≤ 1 :=
  le_of_tendsto' (R.coordinate_tendsto i) (fun n => hf1 i (R.position n))

end Run

end Klr.CoordinateSelection
