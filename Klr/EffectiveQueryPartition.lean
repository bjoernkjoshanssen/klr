module

public import Klr.CoordinateSelection
public import Klr.EffectiveQueryCoordinates
public import Klr.EffectivePoolReservoir
public import Klr.Computability.RelativeComputable

/-!
# Fixed query partitions with second-jump cylinder coordinates

The numerical reservoir construction first selects all scalar coordinates.
Classical weak compactness then supplies representatives with exactly those
coordinates: uniqueness of scalar limits identifies every cylinder integral.
The same reservoirs suffice for the ordinary computable pool construction.
Thus the fixed partitions have both the required pool property and bounded
representatives with uniformly second-jump-computable cylinder integrals.
-/

@[expose] public section

noncomputable section

namespace Klr.EffectiveQueryPartition

open MeasureTheory Filter Encodable
open Klr.Computability Klr.Computability.OracleJump
open EffectiveQueryCoordinates
open scoped Topology

local instance : Encodable ℚ := (inferInstance : Primcodable ℚ).toEncodable

/-- A scalar selection followed by an ordinary simultaneous weak subsequence.
The lower name remains available for each selected finite reservoir. -/
structure Selection (π : ℕ → ScanRule) where
  lowerName : LeftCeReservoir.LowerName (coordinate π)
  run : CoordinateSelection.Run (coordinate π)
  partition : Pool.QueryPartition π run.position

/-- Every uniformly computable family of scans has such a selection. -/
theorem exists_selection (π : ℕ → ScanRule)
    (hπ : Computable (fun p : ℕ × List Bool => (π p.1).query p.2)) :
    Nonempty (Selection π) := by
  let D := EffectiveQueryCoordinates.lowerName π hπ
  obtain ⟨R⟩ := CoordinateSelection.exists_run D
    (coordinate_nonneg π) (coordinate_le_one π)
  obtain ⟨Q⟩ := Pool.exists_queryPartition π R.position
  exact ⟨⟨D, R, Q⟩⟩

namespace Selection

variable {π : ℕ → ScanRule} (S : Selection π)

/-- Cylinder integrals of the bounded representative are the selected scalar limits. -/
theorem cylinder_integral (i : ℕ) (σ : List Bool) :
    (∫ X in cylinder σ, S.partition.representative i X ∂fairCoin) =
      S.run.limit (encode (i, σ) + 1) := by
  have hc := (S.run.coordinate_tendsto (encode (i, σ) + 1)).comp
    S.partition.subseq_strictMono.tendsto_atTop
  simp only [Function.comp_def, coordinate_cylinder_queryL2] at hc
  have hw := (S.partition.weak i).setIntegral (measurableSet_cylinder σ)
  have he := tendsto_nhds_unique hc hw
  calc
    _ = ∫ X in cylinder σ, S.partition.limit i X ∂fairCoin :=
      integral_congr_ae (ae_restrict_of_ae (S.partition.representative_ae_eq i))
    _ = _ := he.symm

/-- A uniform rational name for all cylinder integrals of all representatives. -/
def cylinderApproximation (i : ℕ) (σ : List Bool) (k : ℕ) : ℚ :=
  S.run.approximation (encode (i, σ) + 1) k

theorem cylinderApproximation_computableIn :
    ComputableIn {oracleFunction (zeroJump 2)}
      (fun p : ℕ × List Bool × ℕ => S.cylinderApproximation p.1 p.2.1 p.2.2) := by
  have hindex : Primrec (fun p : ℕ × List Bool × ℕ => encode (p.1, p.2.1) + 1) :=
    Primrec.succ.comp (Primrec.encode.comp
      (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))
  exact RelativeComputable.comp₂ S.run.approximation_computableIn hindex.computableIn
    (Primrec.snd.comp Primrec.snd).computableIn

theorem cylinderApproximation_error (i : ℕ) (σ : List Bool) (k : ℕ) :
    ‖(S.cylinderApproximation i σ k : ℝ) -
      ∫ X in cylinder σ, S.partition.representative i X ∂fairCoin‖ ≤ (1 / 2 : ℝ) ^ k := by
  rw [S.cylinder_integral]
  exact S.run.approximation_error _ _

/-- The weak subsequence keeps the scalar weighted limit selected at coordinate zero. -/
theorem weighted_tendsto :
    Tendsto (Pool.weightedQueryProbability π ∘ S.partition.position) atTop
      (𝓝 (S.run.limit 0)) := by
  apply S.partition.scalar_tendsto
  simpa only [Function.comp_def, coordinate_zero] using S.run.coordinate_tendsto 0

/-- Every positive error has an ordinary c.e. local reservoir for the weighted mass. -/
theorem exists_reservoir {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set ℕ, REPred (fun b => b ∈ U) ∧
      (∀ᶠ n in atTop, S.partition.position n ∈ U) ∧
      ∀ b ∈ U, Pool.weightedQueryProbability π b ≤ S.run.limit 0 + ε := by
  obtain ⟨U, hU, hmem, hupper⟩ := S.run.exists_reservoir S.lowerName 0 hε
  refine ⟨U, hU, ?_, hupper⟩
  exact S.partition.subseq_strictMono.tendsto_atTop.eventually hmem

/-- These same fixed high sets satisfy the original ordinary computable pool contract. -/
theorem computable_pools : PoolConstruction.ComputablePools π S.partition.high :=
  PoolReservoir.exists_computable_pools_of_reservoirs S.partition
    (S.partition.positions_tendsto S.run.position_strictMono.tendsto_atTop)
    S.weighted_tendsto (fun _ hε => S.exists_reservoir hε)

end Selection

/-- The concrete selection for the success-covering family of total simulators. -/
def simulatorSelection : Selection simulatorScan :=
  Classical.choice (exists_selection simulatorScan UniformStrategyFamily.primrec_query.to_comp)

end Klr.EffectiveQueryPartition
