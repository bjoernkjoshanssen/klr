module

public import Klr.Separation

/-!
# Proved Palomar statements

The full proof development is imported here. This file does not import
`Challenge`: its deliberate statement holes cannot enter either proof.
Comparator checks these declarations against the independently compiled
standalone statements and their explicit definitions in `Challenge.lean`.
-/

@[expose] public section

namespace PalomarKlr

/-- The completed affine-block construction produces a separating sequence. -/
theorem separation :
    ∃ X : Klr.Cantor,
      Klr.KolmogorovLovelandRandom X ∧ ¬Klr.MartinLofRandom X := by
  exact Klr.exists_kolmogorovLovelandRandom_not_martinLofRandom

/-- The separation and the proved `MLR → KLR` implication give proper inclusion. -/
theorem strict_inclusion :
    {X : Klr.Cantor | Klr.MartinLofRandom X} ⊂
      {X : Klr.Cantor | Klr.KolmogorovLovelandRandom X} := by
  exact Klr.martinLofRandom_ssubset_kolmogorovLovelandRandom

end PalomarKlr
