module

public import Klr.UniformNormalization
public import Klr.UniformFiniteScan
public import Klr.CodedStageConstruction
public import Klr.EffectiveClosedCodes

/-!
# Uniform computation of the exact finite stage objective

The original finite objective is computable uniformly in the number of
protected simulators, the old affine header and the finite candidate. The
only oracle input is the second-jump normalized-wager family. Finite scan
simulation, support/rank tests, averaging and summation cost no further jump.
-/

@[expose] public section

namespace Klr.UniformStageCost

open RationalComputability SparseSearch SparseListSearch
open Klr.Computability Klr.Computability.OracleJump

local instance : Encodable ℚ := (inferInstance : Primcodable ℚ).toEncodable

theorem computableIn_cond {α β : Type*} [Primcodable α] [Primcodable β]
    {O : Set (ℕ →. ℕ)} {b : α → Bool} {f g : α → β}
    (hb : ComputableIn O b) (hf : ComputableIn O f) (hg : ComputableIn O g) :
    ComputableIn O (fun a => _root_.cond (b a) (f a) (g a)) := by
  have hc : Primrec (fun p : Bool × (β × β) => _root_.cond p.1 p.2.1 p.2.2) :=
    Primrec.cond Primrec.fst (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact RelativeComputable.comp hc.computableIn
    (RelativeComputable.pair hb (RelativeComputable.pair hf hg))

/-- Finite rational averaging preserves an arbitrary oracle. -/
theorem computableIn_average {α : Type*} [Primcodable α] [Inhabited α]
    {O : Set (ℕ →. ℕ)} {n : α → ℕ} {f : α → List Bool → ℚ}
    (hn : ComputableIn O n) (hf : ComputableIn₂ O f) :
    ComputableIn O (fun a => PoolAdvice.average (n a) (f a)) := by
  have hw := RelativeComputable.comp (f := words) computable_words.computableIn hn
  have hs := EffectiveClosedCodes.computableIn_list_sum hw hf
  have hd := RelativeComputable.comp primrec_rat_natCast.computableIn
    (RelativeComputable.comp Primrec.list_length.computableIn hw)
  have h := RelativeComputable.comp₂ (f := fun q r : ℚ => q / r)
    primrec_rat_div.computableIn₂ hs hd
  exact RelativeComputable.of_eq h fun a => by
    simp only [PoolAdvice.average, PoolAdvice.length_words, Nat.cast_pow, Nat.cast_ofNat]

/-- The existing exact conditional expectation formula also preserves the oracle. -/
theorem computableIn_expectation {α : Type*} [Primcodable α] [Inhabited α]
    {O : Set (ℕ →. ℕ)} {n : α → ℕ} {p : α → List Bool → Bool}
    {f : α → List Bool → ℚ}
    (hn : ComputableIn O n) (hp : ComputableIn₂ O p) (hf : ComputableIn₂ O f) :
    ComputableIn O (fun a => StageFiniteCondition.expectation (n a) (p a) (f a)) := by
  have hnum := computableIn_average (n := n)
    (f := fun a s => _root_.cond (p a s) (f a s) (0 : ℚ)) hn
    (computableIn_cond (b := fun x : α × List Bool => p x.1 x.2)
      (f := fun x => f x.1 x.2) (g := fun _ => (0 : ℚ)) hp hf (ComputableIn.const 0))
  have hden := computableIn_average (n := n)
    (f := fun a s => _root_.cond (p a s) (1 : ℚ) 0) hn
    (computableIn_cond (b := fun x : α × List Bool => p x.1 x.2)
      (f := fun _ => (1 : ℚ)) (g := fun _ => (0 : ℚ)) hp
      (ComputableIn.const 1) (ComputableIn.const 0))
  exact RelativeComputable.of_eq
    (RelativeComputable.comp₂ (f := fun q r : ℚ => q / r)
      primrec_rat_div.computableIn₂ hnum hden) fun _ => by
        simp only [StageFiniteCondition.expectation, Bool.cond_eq_ite]

/-- Relative version of the finite support-wager loop. -/
theorem computableIn_truncatedWith {α : Type*} [Primcodable α] [Inhabited α]
    {O : Set (ℕ →. ℕ)} {q : α → List Bool → ℕ} {h : α → List Bool → ℚ}
    {selected : α → ℕ → Bool} {v : α → List Bool}
    (hq : ComputableIn₂ O q) (hh : ComputableIn₂ O h)
    (hs : ComputableIn₂ O selected) (hv : ComputableIn O v) :
    ComputableIn O (fun a => StageFiniteWager.truncatedWith (q a) (h a) (selected a) (v a)) := by
  have hp : ComputableIn O (fun p : α × ℕ => (v p.1).take p.2) :=
    RelativeComputable.comp₂ (f := List.take) Primrec.list_take.computableIn₂
      ComputableIn.snd (RelativeComputable.comp (f := v) hv ComputableIn.fst)
  have hg : ComputableIn O (fun p : α × ℕ => selected p.1 (q p.1 ((v p.1).take p.2))) :=
    RelativeComputable.comp₂ (f := selected) hs ComputableIn.fst
      (RelativeComputable.comp₂ (f := q) hq ComputableIn.fst hp)
  have hw : ComputableIn O (fun p : α × ℕ => |h p.1 ((v p.1).take p.2)|) :=
    RelativeComputable.comp (f := fun r : ℚ => |r|) PoolAdvice.computable_rat_abs.computableIn
      (RelativeComputable.comp₂ (f := h) hh ComputableIn.fst hp)
  have hl : ComputableIn O (fun a => List.range (v a).length) :=
    RelativeComputable.comp Primrec.list_range.computableIn
      (RelativeComputable.comp (f := List.length) Primrec.list_length.computableIn hv)
  have ht := EffectiveClosedCodes.computableIn_list_sum
    (l := fun a => List.range (v a).length)
    (f := fun a t => _root_.cond (selected a (q a ((v a).take t))) |h a ((v a).take t)| (0 : ℚ)) hl
    (computableIn_cond
      (b := fun p : α × ℕ => selected p.1 (q p.1 ((v p.1).take p.2)))
      (f := fun p => |h p.1 ((v p.1).take p.2)|) (g := fun _ => (0 : ℚ))
      hg hw (ComputableIn.const 0))
  exact RelativeComputable.of_eq ht fun _ => by
    simp only [StageFiniteWager.truncatedWith, Bool.cond_eq_ite]

variable {α : Type*} [Primcodable α] [Inhabited α]

/-- Uniform rational statistics for the actual normalized simulator family. -/
theorem statistic_computableIn {i : α → ℕ} {G : α → List ℕ}
    {a : α → Entry} {v : α → List Bool}
    (hi : Computable i) (hG : Computable G) (ha : Computable a) (hv : Computable v) :
    ComputableIn {oracleFunction (zeroJump 2)} (fun p =>
      StageSyndromeObjective.statistic (UniformStrategyFamily.strategy (i p))
        (G p) (a p) (v p)) := by
  have hq : ComputableIn₂ {oracleFunction (zeroJump 2)}
      (fun p w => (UniformStrategyFamily.strategy (i p)).scan.query w) :=
    RelativeComputable.comp₂ (f := fun e w => (UniformStrategyFamily.strategy e).scan.query w)
      UniformStrategyFamily.primrec_query.computableIn
      (RelativeComputable.comp hi.computableIn ComputableIn.fst) ComputableIn.snd
  have hh : ComputableIn₂ {oracleFunction (zeroJump 2)}
      (fun p w =>
        StageFiniteWager.normalizedWager (UniformStrategyFamily.strategy (i p)) w) :=
    RelativeComputable.comp₂ (f := fun e w =>
      StageFiniteWager.normalizedWager (UniformStrategyFamily.strategy e) w)
      UniformNormalization.stageWager_computableIn
      (RelativeComputable.comp hi.computableIn ComputableIn.fst) ComputableIn.snd
  have hs := StageFiniteWager.computable_selected
    (hG.comp Computable.fst) (ha.comp Computable.fst)
    (Computable.snd : Computable (fun p : α × ℕ => p.2))
  have ht := computableIn_truncatedWith
    (q := fun p w => (UniformStrategyFamily.strategy (i p)).scan.query w)
    (h := fun p w =>
      StageFiniteWager.normalizedWager (UniformStrategyFamily.strategy (i p)) w)
    (selected := fun p b => StageFiniteWager.selected (G p) (a p) b) (v := v)
    hq hh hs.computableIn hv.computableIn
  have harg : Computable (fun p : α => (((i p, G p), (a p).2), v p)) :=
    ((hi.pair hG).pair (Computable.snd.comp ha)).pair hv
  have hp := (UniformFiniteScan.computable_partialTest
    EffectiveQueryCoordinates.simulatorScan UniformStrategyFamily.primrec_query.to_comp).comp harg
  have hb := Computable.cond hp (Computable.const (1 : ℚ)) (Computable.const 0)
  have hadd := RelativeComputable.comp₂ (f := fun q r : ℚ => q + r)
    primrec_rat_add.computableIn₂ ht hb.computableIn
  exact RelativeComputable.of_eq hadd fun _ => by
    simp only [StageSyndromeObjective.statistic, StageFiniteWager.truncatedCandidate,
      BettingStrategy.normalize_scan, Bool.cond_eq_ite, EffectiveQueryCoordinates.simulatorScan]
    rfl

/-- Uniform exact conditional cost for one indexed simulator. -/
theorem oneCost_computableIn {i : α → ℕ} {cs : α → List AffineCode.Data}
    {G : α → List ℕ} {a : α → Entry} {V : α → ℕ} {y : α → List Bool}
    (hi : Computable i) (hcs : Computable cs) (hG : Computable G) (ha : Computable a)
    (hV : Computable V) (hy : Computable y) :
    ComputableIn {oracleFunction (zeroJump 2)} (fun p =>
      StageSyndromeObjective.oneCost (UniformStrategyFamily.strategy (i p))
        (cs p) (G p) (a p) (V p) (y p)) := by
  have hw := StageFiniteScan.computable_list_sum (l := cs)
    (f := fun _ c => AffineCode.width c) hcs
    (AffineCode.computable_width.comp Computable.snd)
  have hbranch := (UniformFiniteScan.computable_branchBound
    EffectiveQueryCoordinates.simulatorScan UniformStrategyFamily.primrec_query.to_comp).comp
      (hi.pair hV)
  have hn := Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp hw hbranch)
    (StageCandidateCode.computable_bound.comp hG)
  have hold := StageFiniteProbability.computable_accepts.comp
    (hcs.comp Computable.fst) Computable.snd
  have hnew := StageCandidateCode.computable_table.comp
    ((((hG.comp Computable.fst).pair (Computable.snd.comp (ha.comp Computable.fst))).pair
      (hy.comp Computable.fst)).pair Computable.snd)
  have hp := Primrec.and.to_comp.comp hold hnew
  have hrunarg : Computable (fun p : α × List Bool => ((i p.1, p.2), V p.1)) :=
    ((hi.comp Computable.fst).pair Computable.snd).pair (hV.comp Computable.fst)
  have hr := (UniformFiniteScan.computable_run
    EffectiveQueryCoordinates.simulatorScan UniformStrategyFamily.primrec_query.to_comp).comp
      hrunarg
  have hf := statistic_computableIn (hi.comp Computable.fst) (hG.comp Computable.fst)
    (ha.comp Computable.fst) hr
  have h := computableIn_expectation
    (n := fun p => ((cs p).map AffineCode.width).sum +
      StageFiniteScan.branchBound (EffectiveQueryCoordinates.simulatorScan (i p)) (V p) +
      StageCandidateCode.bound (G p))
    (p := fun p s => StageFiniteProbability.accepts (cs p) s &&
      StageCandidateCode.table (G p) (a p).2 (y p) s)
    (f := fun p s => StageSyndromeObjective.statistic (UniformStrategyFamily.strategy (i p))
      (G p) (a p) (StageFiniteScan.run (EffectiveQueryCoordinates.simulatorScan (i p)) s (V p)))
    hn.computableIn hp.computableIn hf
  exact RelativeComputable.of_eq h fun _ => rfl

/-- All finite parameters, including the protected-list length, vary uniformly. -/
theorem cost_computableIn : ComputableIn {oracleFunction (zeroJump 2)}
    (fun p : ℕ × (List AffineCode.Data × FiniteStageCandidate.Candidate) =>
      CodedStageConstruction.cost (StagePrepared.protectedRules UniformStrategyFamily.strategy p.1)
        p.2.1 p.2.2) := by
  let Param := ℕ × (List AffineCode.Data × FiniteStageCandidate.Candidate)
  have hn : Computable (fun p : Param => List.range (p.1 + 1)) :=
    Primrec.list_range.to_comp.comp (Computable.succ.comp Computable.fst)
  have hcs : Computable (fun p : Param × ℕ => p.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hc : Computable (fun p : Param × ℕ => p.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hd := FiniteStageCandidate.primrec_data.to_comp.comp hc
  have hf := oneCost_computableIn Computable.snd hcs
    (FiniteStageData.primrec_pool.to_comp.comp hd)
    (FiniteStageData.primrec_entry.to_comp.comp hd)
    (FiniteStageCandidate.primrec_horizon.to_comp.comp hc)
    (FiniteStageData.primrec_syndrome.to_comp.comp hd)
  have hs := EffectiveClosedCodes.computableIn_list_sum
    (l := fun p : Param => List.range (p.1 + 1))
    (f := fun p j => StageSyndromeObjective.oneCost (UniformStrategyFamily.strategy j) p.2.1
      (FiniteStageData.pool (FiniteStageCandidate.data p.2.2))
      (FiniteStageData.entry (FiniteStageCandidate.data p.2.2))
      (FiniteStageCandidate.horizon p.2.2)
      (FiniteStageData.syndrome (FiniteStageCandidate.data p.2.2))) hn.computableIn hf
  apply RelativeComputable.of_eq hs
  intro p
  unfold CodedStageConstruction.cost StageSyndromeObjective.cost StagePrepared.protectedRules
  rw [List.map_ofFn]
  congr 1
  apply List.ext_getElem (by simp)
  intro j hj hk
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, Function.comp_apply]

theorem cost_computableIn_fourth : ComputableIn {oracleFunction (zeroJump 4)}
    (fun p : ℕ × (List AffineCode.Data × FiniteStageCandidate.Candidate) =>
      CodedStageConstruction.cost (StagePrepared.protectedRules UniformStrategyFamily.strategy p.1)
        p.2.1 p.2.2) :=
  RelativeComputable.transfer cost_computableIn (zeroJump_mono (by decide))

end Klr.UniformStageCost
