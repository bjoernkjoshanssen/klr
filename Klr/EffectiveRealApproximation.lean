module

public import Klr.PoolAdviceComputable
public import Klr.Computability.RelativeComputable

/-!
# Finite certificates for strict real inequalities

Rational approximations with computable error bounds tending to zero let us
certify strict real inequalities by finite rational tests. Neither a fixed
dyadic error convention nor a convergence modulus for the errors is needed.
Finitely many upper and lower inequalities admit a common certificate stage.
-/

@[expose] public section

namespace Klr.EffectiveRealApproximation

open Filter RationalComputability
open Klr.Computability
open scoped Topology

local instance : Encodable ℚ := (inferInstance : Primcodable ℚ).toEncodable

variable {α : Type*} [Primcodable α]

/-- Actual oracle-computable rational approximants and errors. -/
structure Name (A : Oracle) (f : α → ℝ) where
  approximation : α → ℕ → ℚ
  error : α → ℕ → ℚ
  computable_approximation : ComputableIn₂ {oracleFunction A} approximation
  computable_error : ComputableIn₂ {oracleFunction A} error
  bound : ∀ a k, |(approximation a k : ℝ) - f a| ≤ (error a k : ℝ)
  error_tendsto : ∀ a, Tendsto (fun k => (error a k : ℝ)) atTop (𝓝 0)

namespace Name

variable {A : Oracle} {f : α → ℝ} (N : Name A f)

/-- A rational upper certificate. -/
def upper (p : α × ℚ) (k : ℕ) : Bool :=
  decide (N.approximation p.1 k + N.error p.1 k < p.2)

/-- A rational lower certificate. -/
def lower (p : α × ℚ) (k : ℕ) : Bool :=
  decide (p.2 < N.approximation p.1 k - N.error p.1 k)

private theorem approximation_reindex : ComputableIn {oracleFunction A}
    (fun p : (α × ℚ) × ℕ => N.approximation p.1.1 p.2) :=
  RelativeComputable.comp₂ N.computable_approximation
    (RelativeComputable.comp ComputableIn.fst ComputableIn.fst) ComputableIn.snd

private theorem error_reindex : ComputableIn {oracleFunction A}
    (fun p : (α × ℚ) × ℕ => N.error p.1.1 p.2) :=
  RelativeComputable.comp₂ N.computable_error
    (RelativeComputable.comp ComputableIn.fst ComputableIn.fst) ComputableIn.snd

theorem upper_computable : ComputableIn₂ {oracleFunction A} N.upper := by
  have hsum := RelativeComputable.comp₂ (f := fun q r : ℚ => q + r)
    primrec_rat_add.computableIn₂ N.approximation_reindex N.error_reindex
  exact RelativeComputable.comp₂ (f := fun q r : ℚ => decide (q < r))
    PoolAdvice.computable_rat_lt.computableIn hsum
    (RelativeComputable.comp ComputableIn.snd ComputableIn.fst)

theorem lower_computable : ComputableIn₂ {oracleFunction A} N.lower := by
  have hsub := RelativeComputable.comp₂ (f := fun q r : ℚ => q - r)
    primrec_rat_sub.computableIn₂ N.approximation_reindex N.error_reindex
  exact RelativeComputable.comp₂ (f := fun q r : ℚ => decide (q < r))
    PoolAdvice.computable_rat_lt.computableIn
    (RelativeComputable.comp ComputableIn.snd ComputableIn.fst) hsub

theorem upper_sound {a : α} {r : ℚ} {k : ℕ} (h : N.upper (a, r) k = true) :
    f a < (r : ℝ) := by
  have hc : (N.approximation a k : ℝ) + (N.error a k : ℝ) < (r : ℝ) := by
    exact_mod_cast (of_decide_eq_true h : N.approximation a k + N.error a k < r)
  have hb := N.bound a k
  linarith [neg_le_abs ((N.approximation a k : ℝ) - f a)]

theorem lower_sound {a : α} {r : ℚ} {k : ℕ} (h : N.lower (a, r) k = true) :
    (r : ℝ) < f a := by
  have hc : (r : ℝ) < (N.approximation a k : ℝ) - (N.error a k : ℝ) := by
    exact_mod_cast (of_decide_eq_true h : r < N.approximation a k - N.error a k)
  have hb := N.bound a k
  linarith [le_abs_self ((N.approximation a k : ℝ) - f a)]

theorem eventually_upper {a : α} {r : ℚ} (h : f a < (r : ℝ)) :
    ∀ᶠ k in atTop, N.upper (a, r) k = true := by
  have hs := (tendsto_order.mp (N.error_tendsto a)).2
    (((r : ℝ) - f a) / 2) (by linarith)
  filter_upwards [hs] with k hk
  apply decide_eq_true
  apply (Rat.cast_lt (K := ℝ)).mp
  push_cast
  have hb := N.bound a k
  linarith [le_abs_self ((N.approximation a k : ℝ) - f a)]

theorem eventually_lower {a : α} {r : ℚ} (h : (r : ℝ) < f a) :
    ∀ᶠ k in atTop, N.lower (a, r) k = true := by
  have hs := (tendsto_order.mp (N.error_tendsto a)).2
    ((f a - (r : ℝ)) / 2) (by linarith)
  filter_upwards [hs] with k hk
  apply decide_eq_true
  apply (Rat.cast_lt (K := ℝ)).mp
  push_cast
  have hb := N.bound a k
  linarith [neg_le_abs ((N.approximation a k : ℝ) - f a)]

theorem exists_upper_iff (a : α) (r : ℚ) :
    (∃ k, N.upper (a, r) k = true) ↔ f a < (r : ℝ) :=
  ⟨fun ⟨_, h⟩ => N.upper_sound h, fun h => (N.eventually_upper h).exists⟩

theorem exists_lower_iff (a : α) (r : ℚ) :
    (∃ k, N.lower (a, r) k = true) ↔ (r : ℝ) < f a :=
  ⟨fun ⟨_, h⟩ => N.lower_sound h, fun h => (N.eventually_lower h).exists⟩

end Name

/-- `true` asks for an upper bound, `false` for a lower bound. -/
abbrev Constraint (α : Type*) := Bool × (α × ℚ)

def Holds (f : α → ℝ) (c : Constraint α) : Prop :=
  if c.1 then f c.2.1 < (c.2.2 : ℝ) else (c.2.2 : ℝ) < f c.2.1

namespace Name

variable {A : Oracle} {f : α → ℝ} (N : Name A f)

def certificate (c : Constraint α) (k : ℕ) : Bool :=
  if c.1 then N.upper c.2 k else N.lower c.2 k

theorem certificate_computable : ComputableIn₂ {oracleFunction A} N.certificate := by
  have hu : ComputableIn {oracleFunction A}
      (fun p : Constraint α × ℕ => N.upper p.1.2 p.2) :=
    RelativeComputable.comp₂ N.upper_computable
      (RelativeComputable.comp ComputableIn.snd ComputableIn.fst) ComputableIn.snd
  have hl : ComputableIn {oracleFunction A}
      (fun p : Constraint α × ℕ => N.lower p.1.2 p.2) :=
    RelativeComputable.comp₂ N.lower_computable
      (RelativeComputable.comp ComputableIn.snd ComputableIn.fst) ComputableIn.snd
  have hc : Primrec (fun p : Bool × (Bool × Bool) => if p.1 then p.2.1 else p.2.2) :=
    (Primrec.cond Primrec.fst (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).of_eq fun _ => by simp only [Bool.cond_eq_ite]
  exact RelativeComputable.comp hc.computableIn
    (RelativeComputable.pair (Primrec.fst.comp Primrec.fst).computableIn
      (RelativeComputable.pair hu hl))

theorem certificate_sound {c : Constraint α} {k : ℕ}
    (h : N.certificate c k = true) : Holds f c := by
  rcases c with ⟨b, a, r⟩
  cases b
  · exact N.lower_sound h
  · exact N.upper_sound h

theorem eventually_certificate {c : Constraint α} (h : Holds f c) :
    ∀ᶠ k in atTop, N.certificate c k = true := by
  rcases c with ⟨b, a, r⟩
  cases b
  · exact N.eventually_lower h
  · exact N.eventually_upper h

variable [Inhabited α]

/-- A single finite loop checks a whole list at one common precision. -/
def certificates (L : List (Constraint α)) (k : ℕ) : Bool :=
  ((List.range L.length).map (fun j => N.certificate (L.getD j default) k)).all id

theorem certificates_computable : ComputableIn₂ {oracleFunction A} N.certificates := by
  have hj : Primrec (fun p : (List (Constraint α) × ℕ) × ℕ =>
      p.1.1.getD p.2 default) :=
    (Primrec.list_getD default).comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hc : ComputableIn₂ {oracleFunction A}
      (fun p : List (Constraint α) × ℕ => fun j => N.certificate (p.1.getD j default) p.2) :=
    RelativeComputable.comp₂ N.certificate_computable hj.computableIn
      (Primrec.snd.comp Primrec.fst).computableIn
  have ht := RelativeComputable.comp (RelativeComputable.tabulate hc)
    (RelativeComputable.pair ComputableIn.id
      (Primrec.list_length.comp Primrec.fst).computableIn)
  have ha : Primrec (fun l : List Bool => l.all id) :=
    Primrec.list_all Primrec.id Primrec.snd.to₂
  exact RelativeComputable.comp ha.computableIn ht

theorem certificates_eq_true (L : List (Constraint α)) (k : ℕ) :
    N.certificates L k = true ↔ ∀ c ∈ L, N.certificate c k = true := by
  simp only [certificates, List.all_map, List.all_eq_true, List.mem_range,
    Function.comp_apply, id_eq, List.forall_mem_iff_getElem]
  constructor <;> intro h j hj
  · simpa only [List.getD_eq_getElem _ default hj] using h j hj
  · simpa only [List.getD_eq_getElem _ default hj] using h j hj

theorem exists_certificates_iff (L : List (Constraint α)) :
    (∃ k, N.certificates L k = true) ↔ ∀ c ∈ L, Holds f c := by
  constructor
  · rintro ⟨k, hk⟩ c hc
    exact N.certificate_sound ((N.certificates_eq_true L k).mp hk c hc)
  · intro h
    have he : ∀ᶠ k in atTop, ∀ c ∈ L, N.certificate c k = true := by
      induction L with
      | nil => exact Eventually.of_forall (by simp)
      | cons c L ih =>
        have hc := N.eventually_certificate (h c (by simp))
        have ht := ih (fun d hd => h d (by simp [hd]))
        filter_upwards [hc, ht] with k hk hL
        simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hk hL
    obtain ⟨k, hk⟩ := he.exists
    exact ⟨k, (N.certificates_eq_true L k).mpr hk⟩

end Name

end Klr.EffectiveRealApproximation
