module

public import Klr.SparseSearchRank

/-!
# Effective completion of full-rank matrix codes

The input matrix needs no right-inverse certificate. A partial recursive
search enumerates concrete Boolean certificate lists and checks them with
the existing affine-code verifier. Its domain is proved to be exactly the
full-row-rank matrices. Whenever it halts, it supplies a valid certificate
for the original matrix and syndrome.
-/

@[expose] public section

namespace Klr.SparseSearch

open AffineCode FiniteMeasure

/-- Replace only the certificate field of an affine-system code. -/
def withCertificate (c : Data) (s : List (List Bool)) : Data :=
  (c.1, (rows c, (syndrome c, s)))

@[simp] theorem width_withCertificate (c : Data) (s : List (List Bool)) :
    width (withCertificate c s) = width c := rfl

@[simp] theorem rank_withCertificate (c : Data) (s : List (List Bool)) :
    rank (withCertificate c s) = rank c := rfl

@[simp] theorem matrix_withCertificate (c : Data) (s : List (List Bool)) :
    matrix (withCertificate c s) = matrix c := rfl

@[simp] theorem syndromeVector_withCertificate (c : Data) (s : List (List Bool)) :
    syndromeVector (withCertificate c s) = syndromeVector c := rfl

@[simp] theorem event_withCertificate (c : Data) (s : List (List Bool)) :
    event (withCertificate c s) = event c := rfl

theorem computable_withCertificate : Computable₂ withCertificate := by
  exact ((Computable.fst.comp Computable.fst).pair
    ((computable_rows.comp Computable.fst).pair
      ((computable_syndrome.comp Computable.fst).pair Computable.snd))).to₂

theorem exists_valid_certificate (c : Data)
    (hc : Function.Surjective (matrix c).mulVecLin) :
    ∃ s : List (List Bool), valid (withCertificate c s) = true := by
  obtain ⟨R, hR⟩ := exists_right_inverse (matrix c) hc
  let s := List.ofFn (fun i => List.ofFn (fun j => boolEquivF2.symm (R i j)))
  have hs : rightMatrix (withCertificate c s) = R := by
    ext i j
    change Fin (width c) at i
    change Fin (rank c) at j
    simp [rightMatrix, certificate, withCertificate, entry, s]
  refine ⟨s, (valid_iff_right_inverse _).mpr ?_⟩
  rw [hs]
  change matrix c * R = 1
  exact hR

/-- One search step decodes one ordinary natural-number code and verifies it. -/
def certificateTrial (c : Data) (n : ℕ) : Option (List (List Bool)) :=
  (Encodable.decode n).bind (fun s => if valid (withCertificate c s) then some s else none)

theorem computable_certificateTrial : Computable₂ certificateTrial := by
  have hv := computable_valid.comp computable_withCertificate
  have hf : Computable₂ (fun c s =>
      if valid (withCertificate c s) then some s else none) := by
    have h := Computable.cond hv (Computable.option_some.comp Computable.snd)
      (Computable.const none)
    exact h.of_eq fun _ => by simp [Bool.cond_eq_ite]
  exact Computable.bind_decode_iff.mpr hf

/-- Actual unbounded enumeration of candidate right-inverse certificates. -/
def completeCertificate (c : Data) : Part (List (List Bool)) :=
  Nat.rfindOpt (certificateTrial c)

theorem partrec_completeCertificate : Partrec completeCertificate :=
  Partrec.rfindOpt computable_certificateTrial

theorem completeCertificate_spec {c : Data} {s : List (List Bool)}
    (hs : s ∈ completeCertificate c) : valid (withCertificate c s) = true := by
  obtain ⟨n, hn⟩ := Nat.rfindOpt_spec hs
  simp only [certificateTrial, Option.mem_bind_iff] at hn
  obtain ⟨t, _, ht⟩ := hn
  split_ifs at ht with hv
  · have he : t = s := Option.mem_some_iff.mp ht
    simpa only [he] using hv
  · simp at ht

/-- Halting is equivalent to full row rank of the input matrix; existence of
a certificate is proved algebraically and does not require a computable choice. -/
theorem completeCertificate_dom_iff (c : Data) :
    (completeCertificate c).Dom ↔ Function.Surjective (matrix c).mulVecLin := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := Part.dom_iff_mem.mp h
    have ht := surjective_of_valid (withCertificate c s) (completeCertificate_spec hs)
    change Function.Surjective (matrix c).mulVecLin at ht
    exact ht
  · intro h
    obtain ⟨s, hs⟩ := exists_valid_certificate c h
    apply Nat.rfindOpt_dom.mpr
    refine ⟨Encodable.encode s, s, ?_⟩
    simp [certificateTrial, hs]

theorem completeCertificate_dom_iff_check (c : Data) :
    (completeCertificate c).Dom ↔ fullRank c = true :=
  (completeCertificate_dom_iff c).trans (fullRank_eq_true c).symm

/-- Supply the found certificate as a complete affine-system output code. -/
def completeCode (c : Data) : Part Data := (completeCertificate c).map (withCertificate c)

theorem partrec_completeCode : Partrec completeCode :=
  partrec_completeCertificate.map computable_withCertificate

theorem completeCode_spec {c d : Data} (hd : d ∈ completeCode c) :
    valid d = true ∧ width d = width c ∧ rank d = rank c ∧
      HEq (matrix d) (matrix c) ∧ HEq (syndromeVector d) (syndromeVector c) ∧
      event d = event c := by
  obtain ⟨s, hs, rfl⟩ := (Part.mem_map_iff _).mp hd
  exact ⟨completeCertificate_spec hs, rfl, rfl, HEq.rfl, HEq.rfl, rfl⟩

theorem completeCode_dom_iff (c : Data) :
    (completeCode c).Dom ↔ Function.Surjective (matrix c).mulVecLin :=
  completeCertificate_dom_iff c

end Klr.SparseSearch
