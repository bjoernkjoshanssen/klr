module

public import Klr.EffectiveStageProbability
public import Klr.FiniteStageHistory

/-!
# Finite lists of stage probability requests

The infinite-horizon obligations of a stage form an ordinary finite list of
strict upper-bound requests. Tags distinguish tail, high/no-drop and low/drop
probabilities. The list includes every protected simulator and every earlier
conditioning prefix, with the actual dyadic stage error.
-/

@[expose] public section

namespace Klr.StageProbabilityRequests

open FiniteStageCandidate FiniteStageHistory EffectiveRealApproximation
open RationalComputability

local instance : Encodable ℚ := (inferInstance : Primcodable ℚ).toEncodable

abbrev Request := Constraint EffectiveStageProbability.Input

/-- The rational error budget is an ordinary primitive recursive function. -/
theorem primrec_error : Primrec StageErrorBudget.rational :=
  (primrec_rat_div.comp Klr.Computability.CauchyModulus.primrec_dyadic
    (Primrec.const 100)).of_eq fun _ => rfl

private theorem primrec_upperRequest {α : Type*} [Primcodable α]
    {tag i : α → ℕ} {cs : α → List AffineCode.Data}
    {c : α → Candidate} {r : α → ℚ}
    (ht : Primrec tag) (hcs : Primrec cs) (hi : Primrec i)
    (hc : Primrec c) (hr : Primrec r) : Primrec (fun p : α =>
      (true, ((tag p, cs p, (i p, data (c p)), horizon (c p)), r p))) :=
  (Primrec.const true).pair
    ((ht.pair (hcs.pair ((hi.pair (primrec_data.comp hc)).pair
      (primrec_horizon.comp hc)))).pair hr)

def tailRequest (p : History × Candidate) (i : ℕ) : Request :=
  (true, ((0, output p.2 :: codes p.1, (i, data p.2), horizon p.2),
    2 * StageErrorBudget.rational p.1.length))

def highRequest (p : History × Candidate) (i : ℕ) : Request :=
  (true, ((1, codes p.1, (i, data p.2), horizon p.2),
    StageErrorBudget.rational p.1.length))

def lowRequest (p : History × Candidate) (a i : ℕ) : Request :=
  (true, ((2, codes (p.1.take a), (i, data p.2), horizon p.2),
    StageErrorBudget.rational p.1.length))

theorem primrec_tailRequest : Primrec₂ tailRequest := by
  have hh : Primrec (fun p : (History × Candidate) × ℕ => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hc : Primrec (fun p : (History × Candidate) × ℕ => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  exact primrec_upperRequest (Primrec.const 0)
    (Primrec.list_cons.comp (primrec_output.comp hc) (primrec_codes.comp hh))
    Primrec.snd hc
    (primrec_rat_mul.comp (Primrec.const 2) (primrec_error.comp (Primrec.list_length.comp hh)))

theorem primrec_highRequest : Primrec₂ highRequest := by
  have hh : Primrec (fun p : (History × Candidate) × ℕ => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hc : Primrec (fun p : (History × Candidate) × ℕ => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  exact primrec_upperRequest (Primrec.const 1) (primrec_codes.comp hh) Primrec.snd hc
    (primrec_error.comp (Primrec.list_length.comp hh))

theorem primrec_lowRequest :
    Primrec (fun p : (History × Candidate) × (ℕ × ℕ) => lowRequest p.1 p.2.1 p.2.2) := by
  have hh : Primrec (fun p : (History × Candidate) × (ℕ × ℕ) => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hc : Primrec (fun p : (History × Candidate) × (ℕ × ℕ) => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  exact primrec_upperRequest (Primrec.const 2)
    (primrec_codes.comp (Primrec.list_take.comp (Primrec.fst.comp Primrec.snd) hh))
    (Primrec.snd.comp Primrec.snd) hc (primrec_error.comp (Primrec.list_length.comp hh))

/-- All strict probability requests of one finite stage, at the original budget. -/
def requests (h : History) (c : Candidate) : List Request :=
  (List.range (h.length + 1)).map (tailRequest (h, c)) ++
    (List.range (h.length + 1)).map (highRequest (h, c)) ++
    (List.range (h.length + 1)).flatMap (fun a =>
      (List.range (h.length + 1)).map (lowRequest (h, c) a))

theorem primrec_requests : Primrec₂ requests := by
  have hn : Primrec (fun p : History × Candidate => List.range (p.1.length + 1)) :=
    Primrec.list_range.comp (Primrec.succ.comp (Primrec.list_length.comp Primrec.fst))
  have ht := Primrec.list_map hn primrec_tailRequest
  have hh := Primrec.list_map hn primrec_highRequest
  have hlow : Primrec₂ (fun p : (History × Candidate) × ℕ => fun i =>
      lowRequest p.1 p.2 i) :=
    primrec_lowRequest.comp
      ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))
  have hl : Primrec₂ (fun p : History × Candidate => fun a =>
      (List.range (p.1.length + 1)).map (lowRequest p a)) :=
    Primrec.list_map (hn.comp Primrec.fst) hlow
  exact (Primrec.list_append.comp (Primrec.list_append.comp ht hh)
    (Primrec.list_flatMap hn hl)).of_eq fun _ => by simp only [requests, List.append_assoc]

theorem computable_requests : Computable₂ requests := primrec_requests.to_comp

/-- The finite syntax lists exactly the three families of strict real inequalities. -/
theorem all_holds_iff (h : History) (c : Candidate) :
    (∀ r ∈ requests h c, Holds EffectiveStageProbability.probability r) ↔
      (∀ i, i ≤ h.length →
        EffectiveStageProbability.probability
          (0, output c :: codes h, (i, data c), horizon c) <
          ((2 * StageErrorBudget.rational h.length : ℚ) : ℝ)) ∧
      (∀ i, i ≤ h.length →
        EffectiveStageProbability.probability
          (1, codes h, (i, data c), horizon c) <
          (StageErrorBudget.rational h.length : ℝ)) ∧
      (∀ a, a ≤ h.length → ∀ i, i ≤ h.length →
        EffectiveStageProbability.probability
          (2, codes (h.take a), (i, data c), horizon c) <
          (StageErrorBudget.rational h.length : ℝ)) := by
  simp only [requests, List.forall_mem_append, List.forall_mem_map, List.forall_mem_flatMap,
    List.mem_range, Nat.lt_succ_iff, tailRequest, highRequest, lowRequest, Holds, ite_true]
  tauto

end Klr.StageProbabilityRequests
