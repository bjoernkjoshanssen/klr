module

public import Klr.EffectiveClosedCodes
public import Klr.UniformStrategyFamily
public import Klr.UniformFiniteScan

/-!
# A one-jump KL-random point in the support of a computable measure

Bounded capital for each member of the ordinary effective simulator family
is an increasing union of closed classes. Their finite-history restrictions
have uniformly ordinary computable clopen approximants. The closed-selection
theorem therefore applies to any measure with oracle-computable exact rational
cylinder masses under which almost every point is KL-random.
-/

@[expose] public section

namespace Klr.EffectiveKLSelection

open MeasureTheory RationalComputability _root_.Klr.Computability
  EffectiveClosedSelection

local instance : Encodable ℚ := (inferInstance : Primcodable ℚ).toEncodable

def scan (e : ℕ) : ScanRule := (UniformStrategyFamily.strategy e).scan

theorem computable_query : Computable (fun p : ℕ × List Bool => (scan p.1).query p.2) :=
  UniformStrategyFamily.primrec_query.to_comp

def capitalClass (e b : ℕ) : Set Cantor :=
  {X | ∀ n, UniformStrategyFamily.value e ((scan e).transcript X n) ≤ (b : ℚ)}

def capitalCode (e b n : ℕ) : RationalPrefixCode.Code :=
  RationalPrefixCode.ofTable (StageFiniteScan.branchBound (scan e) n)
    (fun w => if UniformStrategyFamily.value e (StageFiniteScan.run (scan e) w n) ≤ (b : ℚ)
      then 1 else 0)

theorem event_capitalCode (e b n : ℕ) :
    RationalPrefixCode.event (capitalCode e b n) =
      {X | UniformStrategyFamily.value e ((scan e).transcript X n) ≤ (b : ℚ)} := by
  ext X
  simp only [capitalCode, RationalPrefixCode.event, RationalPrefixCode.eval_ofTable,
    StageFiniteScan.run_inputPrefix_of_bound (scan e) n _
      (StageFiniteScan.query_lt_branchBound (scan e) n) X le_rfl,
    Set.mem_ofPred_eq]
  split_ifs with h
  · norm_num
    exact h
  · norm_num
    exact lt_of_not_ge h

theorem isClosed_capitalClass (e b : ℕ) : IsClosed (capitalClass e b) := by
  have he : capitalClass e b = ⋂ n, RationalPrefixCode.event (capitalCode e b n) := by
    ext X
    simp only [capitalClass, Set.mem_ofPred_eq, Set.mem_iInter, event_capitalCode]
  rw [he]
  exact isClosed_iInter (fun n => (RationalPrefixCode.isClopen_event _).isClosed)

theorem capitalClass_mono (e : ℕ) : Monotone (capitalClass e) := by
  intro b c hbc X hX n
  exact (hX n).trans (by exact_mod_cast hbc)

theorem exists_capitalClass_iff (e : ℕ) (X : Cantor) :
    (∃ b, X ∈ capitalClass e b) ↔ ¬ (UniformStrategyFamily.strategy e).Succeeds X := by
  constructor
  · rintro ⟨b, hb⟩ hs
    obtain ⟨n, hn⟩ := hs (b : ℝ)
    have hle : (UniformStrategyFamily.value e ((scan e).transcript X n) : ℝ) ≤ (b : ℝ) := by
      exact_mod_cast hb n
    exact (not_lt_of_ge hle) hn
  · intro h
    change ¬ ∀ bound : ℝ, ∃ n, bound <
      (UniformStrategyFamily.strategy e).capital.value ((scan e).transcript X n) at h
    push Not at h
    obtain ⟨B, hB⟩ := h
    obtain ⟨b, hb⟩ := exists_nat_ge B
    refine ⟨b, fun n => ?_⟩
    have hle := (hB n).trans hb
    rw [UniformStrategyFamily.strategy_value] at hle
    exact_mod_cast hle

theorem all_capitalClass_iff (X : Cantor) :
    (∀ e, ∃ b, X ∈ capitalClass e b) ↔ KolmogorovLovelandRandom X := by
  simp only [exists_capitalClass_iff, UniformStrategyFamily.kolmogorovLovelandRandom_iff]

theorem capitalClass_full (μ : Measure Cantor) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ X ∂μ, KolmogorovLovelandRandom X) (e : ℕ) :
    μ (⋃ b, capitalClass e b) = 1 := by
  have hae : ∀ᵐ X ∂μ, X ∈ ⋃ b, capitalClass e b := by
    filter_upwards [hμ] with X hX
    exact Set.mem_iUnion.mpr ((exists_capitalClass_iff e X).mpr (hX _))
  simpa only [Set.ofPred_mem_eq, measure_univ] using measure_congr (ae_eq_univ.mpr hae)

/-- The bound for requirement `e`, read in chronological order from the history. -/
def bound (h : History) (e : ℕ) : ℕ := (h.reverse.getD e (0, false)).1

theorem primrec_bound : Primrec₂ bound :=
  Primrec.fst.comp ((Primrec.list_getD (0, false)).comp
    (Primrec.list_reverse.comp Primrec.fst) Primrec.snd)

theorem bound_cons_lt (a : ℕ × Bool) (h : History) {e : ℕ} (he : e < h.length) :
    bound (a :: h) e = bound h e := by
  simp only [bound, List.reverse_cons]
  rw [List.getD_append _ _ _ _ (by simpa using he)]

theorem bound_cons_last (a : ℕ × Bool) (h : History) : bound (a :: h) h.length = a.1 := by
  simp only [bound, List.reverse_cons]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem region_eq (h : History) :
    region capitalClass h = cylinder (word h) ∩
      {X | ∀ e < h.length, X ∈ capitalClass e (bound h e)} := by
  induction h with
  | nil => simp
  | cons a h ih =>
    ext X
    simp only [region, ih, Set.mem_inter_iff, Set.mem_ofPred_eq, List.length_cons]
    constructor
    · rintro ⟨⟨⟨hp, hreq⟩, hlast⟩, hnew⟩
      refine ⟨hnew, fun e he => ?_⟩
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ he) with he | rfl
      · simpa only [bound_cons_lt a h he] using hreq e he
      · simpa only [bound_cons_last] using hlast
    · rintro ⟨hnew, hreq⟩
      have hp : X ∈ cylinder (word h) := by
        rw [word_cons, Splitting.cylinder_snoc] at hnew
        exact hnew.1
      refine ⟨⟨⟨hp, fun e he => ?_⟩, ?_⟩, hnew⟩
      · simpa only [bound_cons_lt a h he] using hreq e (Nat.lt_succ_of_lt he)
      · simpa only [bound_cons_last] using hreq h.length (Nat.lt_succ_self _)

/-- An explicit input depth covering all tested scans and the selected prefix. -/
def depth (h : History) (t : ℕ) : ℕ :=
  h.length + ((List.range h.length).map (fun e => StageFiniteScan.branchBound (scan e) t)).sum

theorem length_le_depth (h : History) (t : ℕ) : h.length ≤ depth h t := Nat.le_add_right _ _

theorem branchBound_le_depth (h : History) (t : ℕ) {e : ℕ} (he : e < h.length) :
    StageFiniteScan.branchBound (scan e) t ≤ depth h t := by
  have hm : StageFiniteScan.branchBound (scan e) t ∈
      (List.range h.length).map (fun e => StageFiniteScan.branchBound (scan e) t) :=
    List.mem_map.mpr ⟨e, List.mem_range.mpr he, rfl⟩
  exact (List.le_sum_of_mem hm).trans (Nat.le_add_left _ _)

def check (h : History) (t : ℕ) (w : List Bool) : Bool :=
  decide (w.take h.length = word h) &&
    EffectiveScan.boundedAll (fun e => EffectiveScan.boundedAll
      (fun n => decide (UniformStrategyFamily.value e (StageFiniteScan.run (scan e) w n) ≤
        (bound h e : ℚ))) t) h.length

theorem check_inputPrefix (h : History) (t : ℕ) (X : Cantor) :
    check h t (ScanRule.inputPrefix X (depth h t)) = true ↔
      X ∈ cylinder (word h) ∧ ∀ e < h.length, ∀ n < t,
        UniformStrategyFamily.value e ((scan e).transcript X n) ≤ (bound h e : ℚ) := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq,
    EffectiveScan.boundedAll_eq_true]
  rw [PoolAdvice.inputPrefix_take X (length_le_depth h t),
    PoolAdvice.inputPrefix_eq_iff_mem_cylinder X h.length (word h) (length_word h)]
  apply and_congr Iff.rfl
  apply forall₂_congr
  intro e he
  apply forall₂_congr
  intro n hn
  rw [StageFiniteScan.run_inputPrefix_of_bound (scan e) t _
    (fun v hv => (StageFiniteScan.query_lt_branchBound (scan e) t v hv).trans_le
      (branchBound_le_depth h t he)) X hn.le]

def code (h : History) (t : ℕ) : RationalPrefixCode.Code :=
  RationalPrefixCode.ofTable (depth h t) (fun w => if check h t w then 1 else 0)

theorem event_code (h : History) (t : ℕ) :
    RationalPrefixCode.event (code h t) =
      cylinder (word h) ∩ {X | ∀ e < h.length, ∀ n < t,
        UniformStrategyFamily.value e ((scan e).transcript X n) ≤ (bound h e : ℚ)} := by
  ext X
  have hc := check_inputPrefix h t X
  simp only [code, RationalPrefixCode.event, RationalPrefixCode.eval_ofTable,
    Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [← hc]
  cases check h t (ScanRule.inputPrefix X (depth h t)) <;> norm_num

theorem code_antitone (h : History) : Antitone (fun t => RationalPrefixCode.event (code h t)) := by
  intro s t hst
  dsimp only
  rw [event_code, event_code]
  exact fun X hX => ⟨hX.1, fun e he n hn => hX.2 e he n (hn.trans_le hst)⟩

theorem code_intersection (h : History) :
    (⋂ t, RationalPrefixCode.event (code h t)) = region capitalClass h := by
  rw [region_eq]
  ext X
  simp only [Set.mem_iInter, event_code, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · intro hX
    exact ⟨(hX 0).1, fun e he n => (hX (n + 1)).2 e he n (Nat.lt_succ_self _)⟩
  · rintro ⟨hp, hX⟩ t
    exact ⟨hp, fun e he n _ => hX e he n⟩

theorem computable_depth : Computable₂ depth := by
  have hb : Computable (fun p : (History × ℕ) × ℕ =>
      StageFiniteScan.branchBound (scan p.2) p.1.2) :=
    Computable.comp
      (f := fun p : ℕ × ℕ => StageFiniteScan.branchBound (scan p.1) p.2)
      (g := fun p : (History × ℕ) × ℕ => (p.2, p.1.2))
      (UniformFiniteScan.computable_branchBound scan computable_query)
      (Computable.snd.pair (Computable.snd.comp Computable.fst))
  have hs := StageFiniteScan.computable_list_sum
    (l := fun p : History × ℕ => List.range p.1.length)
    (f := fun p e => StageFiniteScan.branchBound (scan e) p.2)
    (Primrec.list_range.to_comp.comp (Computable.list_length.comp Computable.fst)) hb
  exact Primrec.nat_add.to_comp.comp (Computable.list_length.comp Computable.fst) hs

private abbrev TestInput := (History × ℕ) × List Bool
private abbrev RuleInput := TestInput × ℕ

theorem computable_check :
    Computable (fun p : (History × ℕ) × List Bool => check p.1.1 p.1.2 p.2) := by
  have he : Computable (fun p : RuleInput × ℕ => p.1.2) :=
    Computable.snd.comp Computable.fst
  have hw : Computable (fun p : RuleInput × ℕ => p.1.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  have hh : Computable (fun p : RuleInput × ℕ => p.1.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))
  have hr : Computable (fun p : RuleInput × ℕ =>
      StageFiniteScan.run (scan p.1.2) p.1.1.2 p.2) :=
    Computable.comp
      (f := fun p : (ℕ × List Bool) × ℕ => StageFiniteScan.run (scan p.1.1) p.1.2 p.2)
      (g := fun p : RuleInput × ℕ => ((p.1.2, p.1.1.2), p.2))
      (UniformFiniteScan.computable_run scan computable_query)
      ((he.pair hw).pair Computable.snd)
  have hv := UniformStrategyFamily.primrec_value.to_comp.comp he hr
  have hbound := primrec_rat_natCast.to_comp.comp (primrec_bound.to_comp.comp hh he)
  have htest : Computable₂ (fun p : RuleInput => fun n =>
      decide (UniformStrategyFamily.value p.2 (StageFiniteScan.run (scan p.2) p.1.2 n) ≤
        (bound p.1.1.1 p.2 : ℚ))) := primrec_rat_le.decide.to_comp.comp hv hbound
  have ht : Computable (fun p : RuleInput => p.1.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  have hinner := (EffectiveScan.computable_boundedAll htest).comp (Computable.id.pair ht)
  have hlen : Computable (fun p : TestInput => p.1.1.length) :=
    Computable.list_length.comp (Computable.fst.comp Computable.fst)
  have houter := (EffectiveScan.computable_boundedAll hinner.to₂).comp
    (Computable.id.pair hlen)
  have hprefix : Computable (fun p : TestInput => decide (p.2.take p.1.1.length = word p.1.1)) :=
    Primrec.eq.decide.to_comp.comp
      (Primrec.list_take.to_comp.comp hlen Computable.snd)
      (primrec_word.to_comp.comp (Computable.fst.comp Computable.fst))
  have h := Primrec.and.to_comp.comp hprefix houter
  exact h.of_eq fun _ => rfl

/-- All finite-history closed approximants are ordinary computable. -/
theorem computable_code : Computable₂ code := by
  have hp : Computable₂ (fun p : History × ℕ => fun w =>
      _root_.cond (check p.1 p.2 w) (1 : ℚ) 0) :=
    Computable.cond computable_check (Computable.const (1 : ℚ)) (Computable.const 0)
  have h := RationalPrefixCode.computable_ofTable
    (d := fun p : History × ℕ => depth p.1 p.2)
    (q := fun p : History × ℕ => fun w => _root_.cond (check p.1 p.2 w) (1 : ℚ) 0)
    computable_depth hp
  exact h.of_eq fun _ => by simp only [code, Bool.cond_eq_ite]

/-- From an almost-surely KL-random measure with exact oracle-computable
cylinder probabilities, one additional jump computes a KL-random support point. -/
theorem exists_klr {A : Oracle} (μ : Measure Cantor) [IsProbabilityMeasure μ]
    (q : List Bool → ℚ) (hqcomp : ComputableIn {oracleFunction A} q)
    (hq : ∀ s, (q s : ℝ) = μ.real (cylinder s))
    (hμ : ∀ᵐ X ∂μ, KolmogorovLovelandRandom X) :
    ∃ X : Cantor, Reduces X (OracleJump.jump A) ∧ KolmogorovLovelandRandom X ∧
      ∀ n, 0 < μ.real (cylinder (ScanRule.inputPrefix X n)) := by
  obtain ⟨X, hX, hclass, hp⟩ := EffectiveClosedCodes.exists_path μ capitalClass
    isClosed_capitalClass capitalClass_mono (capitalClass_full μ hμ)
    q hqcomp hq code computable_code.computableIn code_antitone code_intersection
  exact ⟨X, hX, (all_capitalClass_iff X).mp hclass, hp⟩

/-- The same point belongs to every full-measure closed set, including all
closed affine constraints of the block product. -/
theorem exists_klr_mem_full_closed {A : Oracle} (μ : Measure Cantor) [IsProbabilityMeasure μ]
    (q : List Bool → ℚ) (hqcomp : ComputableIn {oracleFunction A} q)
    (hq : ∀ s, (q s : ℝ) = μ.real (cylinder s))
    (hμ : ∀ᵐ X ∂μ, KolmogorovLovelandRandom X) :
    ∃ X : Cantor, Reduces X (OracleJump.jump A) ∧ KolmogorovLovelandRandom X ∧
      ∀ F : Set Cantor, IsClosed F → μ F = 1 → X ∈ F := by
  obtain ⟨X, hX, hklr, hp⟩ := exists_klr μ q hqcomp hq hμ
  exact ⟨X, hX, hklr, fun _ hF hfull =>
    mem_closed_of_positive_prefixes μ X hp hF hfull⟩

end Klr.EffectiveKLSelection
