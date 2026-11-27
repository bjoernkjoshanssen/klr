module

public import Klr.EffectiveStageChecker
public import Klr.EffectiveStageRecursion

/-!
# The actual fourth-jump affine construction

The fixed simulator partitions, finite probability approximations, strict
stage checker and invariant-preserving oracle search are now combined.
The resulting run is an actual construction; its effectiveness is proved
from the checker rather than assumed as a further input.
-/

@[expose] public section

noncomputable section

namespace Klr.EffectiveConstruction

open Klr.Computability

/-- The full affine stage construction for the success-covering simulators,
with every finite history and output code computable in the fourth jump. -/
def concreteRun : EffectiveStageRecursion.Run (OracleJump.zeroJump 4)
    UniformStrategyFamily.strategy EffectiveFixedPartitions.high := Classical.choice (by
  apply EffectiveStageRecursion.exists_run UniformStrategyFamily.strategy
    EffectiveFixedPartitions.high EffectiveStageChecker.searchStep_computable
    EffectiveStageChecker.searchStep_complete
  intro h hh t c hc
  exact EffectiveStageChecker.searchStep_sound hh hc)

end Klr.EffectiveConstruction
