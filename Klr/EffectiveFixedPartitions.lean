module

public import Klr.EffectiveQueryPartition
public import Klr.EffectiveHighSet
public import Klr.EffectiveEvent
public import Klr.StageConstruction

/-!
# Effective fixed partitions for the total simulator family

The actual scalar selection has cylinder-integral names in the second jump.
The two-jump high-set construction therefore supplies fourth-jump clopen
names for the same fixed Borel partitions that satisfy the ordinary
computable-pool contract. These partitions support every finite stage of
the original separation construction.
-/

@[expose] public section

noncomputable section

namespace Klr.EffectiveFixedPartitions

open MeasureTheory EffectiveQueryPartition RationalPrefixCode
open Klr.Computability Klr.Computability.OracleJump
open scoped symmDiff

local instance : Encodable ℚ := (inferInstance : Primcodable ℚ).toEncodable

/-- The high sets of any effective query selection have fourth-jump names. -/
def highName {π : ℕ → ScanRule} (S : Selection π) :
    EffectiveEvent.Name (zeroJump 4) S.partition.high := Classical.choice (by
  obtain ⟨c, hc, he⟩ := EffectiveHighSet.exists_highSet_name
    S.cylinderApproximation_computableIn S.cylinderApproximation_error
    S.partition.measurable_representative
    (fun i X => (S.partition.representative_bounds i X).1)
    (fun i X => (S.partition.representative_bounds i X).2)
  exact ⟨⟨c, hc, S.partition.measurableSet_high, he⟩⟩)

/-- The fixed high sets used for all stages of the simulator construction. -/
def high : ℕ → Set Cantor := simulatorSelection.partition.high

/-- An actual fourth-jump approximation algorithm for these exact sets. -/
def simulatorHighName : EffectiveEvent.Name (zeroJump 4) high :=
  highName simulatorSelection

theorem measurableSet_high (i : ℕ) : MeasurableSet (high i) :=
  simulatorHighName.measurable i

/-- Normalization changes capital but leaves each simulator's scan unchanged. -/
theorem computable_pools :
    PoolConstruction.ComputablePools
      (fun i => (UniformStrategyFamily.strategy i).normalize.scan) high :=
  simulatorSelection.computable_pools

/-- The named fixed partitions retain the full finite-stage extension theorem. -/
theorem exists_step (old : ℕ → AffineBlock)
    (hold : Pairwise (fun i j => Disjoint (old i).support (old j).support))
    (n z : ℕ) (error : ℚ) (he : 0 < error) :
    ∃ C V, StageRecursion.Step UniformStrategyFamily.strategy high old n z error C V :=
  StageConstruction.exists_step_of_pools UniformStrategyFamily.strategy high
    measurableSet_high computable_pools old hold n z error he

end Klr.EffectiveFixedPartitions
