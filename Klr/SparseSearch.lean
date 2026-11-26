module

public import Klr.SparseSearchMask
public import Klr.SparseSearchCertificate

/-!
# Effective rank verification and certified output

The finite-list search can use the total Boolean rank checker on every unread
column mask. A successful check also guarantees termination of an actual
partial recursive procedure producing a verified affine code for that
restricted matrix.
-/

@[expose] public section

namespace Klr.SparseSearch

open AffineCode RandomMatrix

/-- Actual computability of the restricted-column surjectivity predicate. -/
theorem computablePred_restrictedRank : ComputablePred
    (fun p : Data × List Bool => Function.Surjective
      (restrictedMap (fun j i => matrix p.1 i j) (selectedColumns p.1 p.2) (K := ZMod 2))) := by
  have hc : ComputablePred (fun p : Data × List Bool => maskedFullRank p.1 p.2 = true) :=
    ComputablePred.computable_iff.mpr
      ⟨fun p => maskedFullRank p.1 p.2, computable_maskedFullRank, rfl⟩
  exact hc.of_eq fun p => maskedFullRank_eq_true p.1 p.2

/-- Search for a certified code after zeroing the unselected columns. -/
def completeMaskedCode (p : Data × List Bool) : Part Data := completeCode (maskCode p.1 p.2)

theorem partrec_completeMaskedCode : Partrec completeMaskedCode :=
  partrec_completeCode.comp computable_maskCode

/-- This concrete search halts exactly when the selected columns preserve
full row rank. -/
theorem completeMaskedCode_dom_iff (c : Data) (d : List Bool) :
    (completeMaskedCode (c, d)).Dom ↔ Function.Surjective
      (restrictedMap (fun j i => matrix c i j) (selectedColumns c d) (K := ZMod 2)) := by
  exact (completeCode_dom_iff (maskCode c d)).trans
    ((fullRank_eq_true (maskCode c d)).symm.trans (maskedFullRank_eq_true c d))

end Klr.SparseSearch
