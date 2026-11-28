module

public import Klr.EffectiveRankEvents
public import Klr.EffectiveFixedPartitions
public import Klr.EffectiveConditionalEvent
public import Klr.EffectiveRealApproximation

/-!
# Fourth-jump names for all infinite-horizon stage probabilities

The three kinds of probability tests are first-drop tails, high/no-drop
intersections, and low/drop intersections. Rank events already have first-jump
names; combining them with the fixed fourth-jump high-set names and finite
affine conditioning stays within the fourth jump. Thus strict tests admit
actual finite rational certificates without a fifth-jump decision procedure.
-/

@[expose] public section

noncomputable section

namespace Klr.EffectiveStageProbability

open MeasureTheory FiniteStageData
open _root_.Klr.Computability

local instance : Encodable ℚ := (inferInstance : Primcodable ℚ).toEncodable

def scans (i : ℕ) : ScanRule := (UniformStrategyFamily.strategy i).normalize.scan

theorem computable_query : Computable (fun p : ℕ × List Bool => (scans p.1).query p.2) :=
  UniformStrategyFamily.primrec_query.to_comp

abbrev RankInput := EffectiveRankEvents.Input

def highEvent (p : RankInput) : Set Cantor :=
  (scans p.1).observationMap ⁻¹' EffectiveFixedPartitions.high p.1 ∩
    NoDrop.noDropEvent (block p.2) (scans p.1)

def lowEvent (p : RankInput) : Set Cantor :=
  (scans p.1).observationMap ⁻¹' (EffectiveFixedPartitions.high p.1)ᶜ ∩
    LateDropBound.hasDrop (block p.2) (scans p.1)

def highName : EffectiveEvent.Name (OracleJump.zeroJump 4) highEvent :=
  (UniformFiniteScan.pullbackName scans computable_query
    (EffectiveFixedPartitions.simulatorHighName.reindex
      (f := fun p : RankInput => p.1) ComputableIn.fst) ComputableIn.fst).inter
      ((EffectiveRankEvents.noDropName scans computable_query).transfer
        OracleJump.firstJump_reduces_fourth)

def lowName : EffectiveEvent.Name (OracleJump.zeroJump 4) lowEvent :=
  (UniformFiniteScan.pullbackName scans computable_query
    (EffectiveFixedPartitions.simulatorHighName.compl.reindex
      (f := fun p : RankInput => p.1) ComputableIn.fst) ComputableIn.fst).inter
      ((EffectiveRankEvents.dropName scans computable_query).transfer
        OracleJump.firstJump_reduces_fourth)

def tailName : EffectiveEvent.Name (OracleJump.zeroJump 4)
    (fun p : RankInput × ℕ =>
      StoppingTranscript.rankDropTailEvent (block p.1.2) (scans p.1.1) p.2) :=
  (EffectiveRankEvents.tailName scans computable_query).transfer
    OracleJump.firstJump_reduces_fourth

/-- Tag zero is the first-drop tail; tag one is high/no-drop; other tags are low/drop. -/
def event (p : ℕ × (RankInput × ℕ)) : Set Cantor :=
  if p.1 = 0 then StoppingTranscript.rankDropTailEvent (block p.2.1.2) (scans p.2.1.1) p.2.2
  else if p.1 = 1 then highEvent p.2.1 else lowEvent p.2.1

def eventName : EffectiveEvent.Name (OracleJump.zeroJump 4) event := by
  let T := tailName.reindex (f := fun p : ℕ × (RankInput × ℕ) => p.2) ComputableIn.snd
  let H := highName.reindex (f := fun p : ℕ × (RankInput × ℕ) => p.2.1)
    (Primrec.fst.comp Primrec.snd).computableIn
  let L := lowName.reindex (f := fun p : ℕ × (RankInput × ℕ) => p.2.1)
    (Primrec.fst.comp Primrec.snd).computableIn
  have h0 : Primrec (fun p : ℕ × (RankInput × ℕ) => decide (p.1 = 0)) :=
    Primrec.eq.decide.comp Primrec.fst (Primrec.const 0)
  have h1 : Primrec (fun p : ℕ × (RankInput × ℕ) => decide (p.1 = 1)) :=
    Primrec.eq.decide.comp Primrec.fst (Primrec.const 1)
  change EffectiveEvent.Name (OracleJump.zeroJump 4) (fun p : ℕ × (RankInput × ℕ) =>
    if p.1 = 0 then StoppingTranscript.rankDropTailEvent (block p.2.1.2) (scans p.2.1.1) p.2.2
    else if p.1 = 1 then highEvent p.2.1 else lowEvent p.2.1)
  simpa only [decide_eq_true_eq] using
    T.select (H.select L _ h1.computableIn) _ h0.computableIn

/-- A tag, a finite conditioning header, and the scan/block/horizon data. -/
abbrev Input := ℕ × (List AffineCode.Data × (RankInput × ℕ))

def probability (p : Input) : ℝ :=
  (StageFiniteProbability.law p.2.1).real (event (p.1, p.2.2))

/-- The exact three stage probability families have uniform fourth-jump names. -/
def probabilityName : EffectiveRealApproximation.Name (OracleJump.zeroJump 4) probability := by
  let N := eventName.reindex (f := fun p : Input => (p.1, p.2.2))
    (Primrec.fst.pair (Primrec.snd.comp Primrec.snd)).computableIn
  have hcs : ComputableIn {oracleFunction (OracleJump.zeroJump 4)}
      (fun p : Input => p.2.1) := (Primrec.fst.comp Primrec.snd).computableIn
  exact {
    approximation := EffectiveConditionalEvent.Name.approximation N (fun p => p.2.1)
    error := EffectiveConditionalEvent.Name.error (fun p : Input => p.2.1)
    computable_approximation := EffectiveConditionalEvent.Name.approximation_computable N hcs
    computable_error := EffectiveConditionalEvent.Name.error_computable hcs
    bound := EffectiveConditionalEvent.Name.approximation_error N (fun p => p.2.1)
    error_tendsto := EffectiveConditionalEvent.Name.error_tendsto (fun p : Input => p.2.1) }

@[simp] theorem probability_tail (cs : List AffineCode.Data) (i : ℕ) (d : BlockData) (V : ℕ) :
    probability (0, cs, (i, d), V) =
      (StageFiniteProbability.law cs).real
        (StoppingTranscript.rankDropTailEvent (block d) (scans i) V) := by
  simp [probability, event]

@[simp] theorem probability_high (cs : List AffineCode.Data) (i : ℕ) (d : BlockData) (V : ℕ) :
    probability (1, cs, (i, d), V) =
      (StageFiniteProbability.law cs).real (highEvent (i, d)) := by
  simp [probability, event]

@[simp] theorem probability_low (cs : List AffineCode.Data) (i : ℕ) (d : BlockData) (V : ℕ) :
    probability (2, cs, (i, d), V) =
      (StageFiniteProbability.law cs).real (lowEvent (i, d)) := by
  simp [probability, event]

end Klr.EffectiveStageProbability
