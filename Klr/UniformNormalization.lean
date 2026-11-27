module

public import Klr.UniformStrategyFamily
public import Klr.EffectiveNormalizationStrategy
public import Klr.StageFiniteWager
public import Klr.Computability.RelativeComputable

/-!
# Uniform oracle computation of the actual normalized simulator wagers

The existing normalization uses the canonical approximation program. For the
effective simulator family its approximation values use the second jump.
Both finite-account folds preserve that oracle, so the rational normalized
wagers used by the stage construction are uniformly second-jump computable.
-/

@[expose] public section

namespace Klr.UniformNormalization

open RationalComputability _root_.Klr.Computability

local instance : Encodable ℚ := (inferInstance : Primcodable ℚ).toEncodable

private theorem foldl_take_succ {σ : Type*} (f : σ → Bool → σ) (s : σ)
    (v : List Bool) (n : ℕ) :
    (v.take (n + 1)).foldl f s =
      if n < v.length then f ((v.take n).foldl f s) (v.getD n false)
      else (v.take n).foldl f s := by
  induction v generalizing n s with
  | nil => simp
  | cons b v ih =>
    cases n with
    | zero => simp
    | succ n => simpa using ih (f s b) n

/-- Uniform finite account folds preserve the oracle used by their transition. -/
theorem foldl_computableIn {σ : Type*} [Primcodable σ] [Inhabited σ]
    {O : Set (ℕ →. ℕ)} {f : ℕ → σ → Bool → σ}
    (hf : ComputableIn O (fun p : ℕ × (σ × Bool) => f p.1 p.2.1 p.2.2))
    (s : σ) : ComputableIn O (fun p : ℕ × List Bool => p.2.foldl (f p.1) s) := by
  have he : Primrec (fun p : (ℕ × List Bool) × (ℕ × σ) => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hv : Primrec (fun p : (ℕ × List Bool) × (ℕ × σ) => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hn : Primrec (fun p : (ℕ × List Bool) × (ℕ × σ) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have ha : Primrec (fun p : (ℕ × List Bool) × (ℕ × σ) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hb := (Primrec.list_getD false).comp hv hn
  have hnext := RelativeComputable.comp hf (he.pair (ha.pair hb)).computableIn
  have htest := (Primrec.nat_lt.comp hn (Primrec.list_length.comp hv)).decide
  have hcond : Primrec (fun p : Bool × (σ × σ) => _root_.cond p.1 p.2.1 p.2.2) :=
    Primrec.cond Primrec.fst (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hstep := RelativeComputable.comp hcond.computableIn
    (RelativeComputable.pair htest.computableIn
      (RelativeComputable.pair hnext ha.computableIn))
  have hrec := RelativeComputable.nat_rec (α := ℕ × List Bool) (β := σ)
    (f := fun _ : ℕ × List Bool => s)
    (g := fun (p : ℕ × List Bool) n a => _root_.cond (decide (n < p.2.length))
      (f p.1 a (p.2.getD n false)) a) (ComputableIn.const s) hstep
  have h := RelativeComputable.comp hrec
    (Primrec.id.pair (Primrec.list_length.comp Primrec.snd)).computableIn
  apply RelativeComputable.of_eq h
  intro p
  have haux : ∀ n, Nat.rec (motive := fun _ => σ) s
      (fun n a => _root_.cond (decide (n < p.2.length))
        (f p.1 a (p.2.getD n false)) a) n = (p.2.take n).foldl (f p.1) s := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      simpa only [foldl_take_succ, Bool.cond_decide] using
        congrArg (fun a => _root_.cond (decide (n < p.2.length))
          (f p.1 a (p.2.getD n false)) a) ih
  simpa using haux p.2.length

noncomputable def approximation (e : ℕ) :
    CapitalApproximation (UniformStrategyFamily.strategy e).capital :=
  CapitalApproximation.ofComputable (UniformStrategyFamily.strategy e).capital
    (UniformStrategyFamily.strategy e).computable_capital

noncomputable def reserve (e : ℕ) : ReservedRationalCapital := (approximation e).reserve

theorem approximation_computableIn :
    ComputableIn {oracleFunction (OracleJump.zeroJump 2)}
      (fun p : ℕ × (List Bool × ℕ) => (approximation p.1).value p.2.1 p.2.2) := by
  have hn : ComputableIn {oracleFunction (OracleJump.zeroJump 2)}
      (fun z : ℕ => Encodable.encode
      ((approximation (Nat.unpair z).1).value
        (CanonicalCapitalApproximation.input (Nat.unpair z).2).1
        (CanonicalCapitalApproximation.input (Nat.unpair z).2).2)) :=
    RecursiveIn.iff_nat.mpr UniformStrategyFamily.canonical_approximation_recursive
  have hd := RelativeComputable.comp
    (f := RelativeComputable.decodeDefault (α := ℚ))
    RelativeComputable.primrec_decodeDefault.computableIn hn
  have hi : Primrec (fun p : ℕ × (List Bool × ℕ) => Nat.pair p.1 (Encodable.encode p.2)) :=
    Primrec₂.natPair.comp Primrec.fst (Primrec.encode.comp Primrec.snd)
  have h := RelativeComputable.comp hd hi.computableIn
  exact RelativeComputable.of_eq h fun p => by
    simp only [Nat.unpair_pair, CanonicalCapitalApproximation.input_encode,
      RelativeComputable.decodeDefault_encode]
    exact congrArg (fun e => (approximation e).value p.2.1 p.2.2)
      (congrArg Prod.fst (Nat.unpair_pair p.1 (Encodable.encode p.2)))

theorem stake_computableIn :
    ComputableIn₂ {oracleFunction (OracleJump.zeroJump 2)}
      (fun e v => (approximation e).stake v) := by
  have hv (b : Bool) : ComputableIn {oracleFunction (OracleJump.zeroJump 2)}
      (fun p : ℕ × List Bool =>
        (approximation p.1).value (p.2 ++ [b]) (p.2.length + 2)) := by
    have hi : Primrec (fun p : ℕ × List Bool => (p.1, (p.2 ++ [b], p.2.length + 2))) :=
      (Primrec.fst.pair
        ((Primrec.list_concat.comp Primrec.snd (Primrec.const b)).pair
          (Primrec.nat_add.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 2))))
    have hc := RelativeComputable.comp approximation_computableIn hi.computableIn
    exact RelativeComputable.of_eq hc fun _ => rfl
  have hc := RelativeComputable.comp₂ (f := fun a b : ℚ => a / b) primrec_rat_div.computableIn₂
    (RelativeComputable.comp₂ (f := fun a b : ℚ => a - b) primrec_rat_sub.computableIn₂
      (hv true) (hv false)) (ComputableIn.const 4)
  exact RelativeComputable.of_eq hc fun _ => rfl

theorem reserveStep_computableIn :
    ComputableIn {oracleFunction (OracleJump.zeroJump 2)}
      (fun p : ℕ × ((List Bool × ℚ) × Bool) => (approximation p.1).reserveStep p.2.1 p.2.2) := by
  have hi : Primrec (fun p : ℕ × ((List Bool × ℚ) × Bool) => (p.1, p.2.1.1)) :=
    Primrec.fst.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
  have hf := RelativeComputable.comp stake_computableIn
    hi.computableIn
  have hsign : ComputableIn {oracleFunction (OracleJump.zeroJump 2)}
      (fun p : ℕ × ((List Bool × ℚ) × Bool) => answerSign p.2.2) :=
    (primrec_answerSign.comp (Primrec.snd.comp Primrec.snd)).computableIn
  have hq : ComputableIn {oracleFunction (OracleJump.zeroJump 2)}
      (fun p : ℕ × ((List Bool × ℚ) × Bool) => p.2.1.2) :=
    (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)).computableIn
  have hvalue := RelativeComputable.comp₂ (f := fun a b : ℚ => a + b)
    primrec_rat_add.computableIn₂ hq
    (RelativeComputable.comp₂ (f := fun a b : ℚ => a * b) primrec_rat_mul.computableIn₂ hsign hf)
  have hprefix : ComputableIn {oracleFunction (OracleJump.zeroJump 2)}
      (fun p : ℕ × ((List Bool × ℚ) × Bool) => p.2.1.1 ++ [p.2.2]) :=
    (Primrec.list_concat.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)).computableIn
  exact RelativeComputable.of_eq (RelativeComputable.pair hprefix hvalue) fun _ => rfl

theorem reserveValue_computableIn :
    ComputableIn₂ {oracleFunction (OracleJump.zeroJump 2)} (fun e v => (reserve e).value v) := by
  have h := foldl_computableIn (f := fun e p b => (approximation e).reserveStep p b)
    reserveStep_computableIn ([], (1 : ℚ))
  have hc := RelativeComputable.comp ComputableIn.snd h
  exact RelativeComputable.of_eq hc fun _ => rfl

theorem sourceWager_computableIn :
    ComputableIn₂ {oracleFunction (OracleJump.zeroJump 2)} (fun e v => (reserve e).wager v) := by
  have hv (b : Bool) : ComputableIn {oracleFunction (OracleJump.zeroJump 2)}
      (fun p : ℕ × List Bool => (reserve p.1).value (p.2 ++ [b])) := by
    have hi : Primrec (fun p : ℕ × List Bool => (p.1, p.2 ++ [b])) :=
      Primrec.fst.pair (Primrec.list_concat.comp Primrec.snd (Primrec.const b))
    have hc := RelativeComputable.comp reserveValue_computableIn hi.computableIn
    exact RelativeComputable.of_eq hc fun _ => rfl
  have hc := RelativeComputable.comp₂ (f := fun a b : ℚ => a / b) primrec_rat_div.computableIn₂
    (RelativeComputable.comp₂ (f := fun a b : ℚ => a - b) primrec_rat_sub.computableIn₂
      (hv true) (hv false))
    (RelativeComputable.comp₂ (f := fun a b : ℚ => a * b) primrec_rat_mul.computableIn₂
      (ComputableIn.const 2) reserveValue_computableIn)
  exact RelativeComputable.of_eq hc fun _ => rfl

theorem normalizationStep_computableIn :
    ComputableIn {oracleFunction (OracleJump.zeroJump 2)}
      (fun p : ℕ × (ReservedRationalCapital.NormalizationState × Bool) =>
        (reserve p.1).normalizationStep p.2.1 p.2.2) := by
  have he : Primrec (fun p : ℕ × (ReservedRationalCapital.NormalizationState × Bool) => p.1) :=
    Primrec.fst
  have hv : Primrec (fun p : ℕ × (ReservedRationalCapital.NormalizationState × Bool) => p.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hq : Primrec (fun p : ℕ × (ReservedRationalCapital.NormalizationState × Bool) =>
      p.2.1.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
  have hc : Primrec (fun p : ℕ × (ReservedRationalCapital.NormalizationState × Bool) =>
      p.2.1.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
  have hb : Primrec (fun p : ℕ × (ReservedRationalCapital.NormalizationState × Bool) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hf := RelativeComputable.comp
    (f := fun p : ℕ × List Bool => (reserve p.1).wager p.2)
    (g := fun p : ℕ × (ReservedRationalCapital.NormalizationState × Bool) => (p.1, p.2.1.1))
    sourceWager_computableIn (he.pair hv).computableIn
  have hden := RelativeComputable.comp₂ (O := {oracleFunction (OracleJump.zeroJump 2)})
    (f := fun a b : ℚ => a * b)
    primrec_rat_mul.computableIn₂ (ComputableIn.const 2)
    (RelativeComputable.comp₂ (f := fun a b : ℚ => a + b)
      primrec_rat_add.computableIn₂ (ComputableIn.const 1) hq.computableIn)
  have hh := RelativeComputable.comp₂ (f := fun a b : ℚ => a / b)
    primrec_rat_div.computableIn₂ hf hden
  have hqq := RelativeComputable.comp₂ (f := fun a b : ℚ => a + b)
    primrec_rat_add.computableIn₂ hq.computableIn
    (RelativeComputable.comp₂ (f := fun a b : ℚ => a * b) primrec_rat_mul.computableIn₂ hf hf)
  have hcapital := RelativeComputable.comp₂ (f := fun a b : ℚ => a * b)
    primrec_rat_mul.computableIn₂ hc.computableIn
    (RelativeComputable.comp₂ (f := fun a b : ℚ => a + b)
      primrec_rat_add.computableIn₂ (ComputableIn.const 1)
      (RelativeComputable.comp₂ (f := fun a b : ℚ => a * b) primrec_rat_mul.computableIn₂
        (primrec_answerSign.comp hb).computableIn hh))
  have hnext := RelativeComputable.pair (Primrec.list_concat.comp hv hb).computableIn
    (RelativeComputable.pair hqq hcapital)
  exact RelativeComputable.of_eq hnext fun _ => by
    simp only [ReservedRationalCapital.normalizationStep, pow_two]

theorem normalizationAccount_computableIn :
    ComputableIn₂ {oracleFunction (OracleJump.zeroJump 2)}
      (fun e v => (reserve e).normalizationAccount v) := by
  have h := foldl_computableIn (f := fun e p b => (reserve e).normalizationStep p b)
    normalizationStep_computableIn ([], (0 : ℚ), (1 : ℚ))
  exact RelativeComputable.of_eq h fun _ => rfl

theorem variation_computableIn :
    ComputableIn₂ {oracleFunction (OracleJump.zeroJump 2)}
      (fun e v => (reserve e).variation v) := by
  have h := RelativeComputable.comp (Primrec.fst.comp Primrec.snd).computableIn
    normalizationAccount_computableIn
  exact RelativeComputable.of_eq h fun _ => rfl

theorem normalizedValue_computableIn :
    ComputableIn₂ {oracleFunction (OracleJump.zeroJump 2)}
      (fun e v => (reserve e).normalizedValue v) := by
  have h := RelativeComputable.comp (Primrec.snd.comp Primrec.snd).computableIn
    normalizationAccount_computableIn
  exact RelativeComputable.of_eq h fun _ => rfl

theorem normalizedFraction_computableIn :
    ComputableIn₂ {oracleFunction (OracleJump.zeroJump 2)}
      (fun e v => (reserve e).normalizedFraction v) := by
  have hden := RelativeComputable.comp₂ (f := fun a b : ℚ => a * b)
    primrec_rat_mul.computableIn₂ (ComputableIn.const 2)
    (RelativeComputable.comp₂ (f := fun a b : ℚ => a + b)
      primrec_rat_add.computableIn₂ (ComputableIn.const 1) variation_computableIn)
  have h := RelativeComputable.comp₂ (f := fun a b : ℚ => a / b)
    primrec_rat_div.computableIn₂ sourceWager_computableIn hden
  exact RelativeComputable.of_eq h fun _ => rfl

/-- The precise rational wager function already used by the finite-stage checker. -/
theorem stageWager_computableIn :
    ComputableIn₂ {oracleFunction (OracleJump.zeroJump 2)}
      (fun e v => StageFiniteWager.normalizedWager (UniformStrategyFamily.strategy e) v) :=
  RelativeComputable.of_eq normalizedFraction_computableIn fun _ => rfl

theorem stageWager_computableIn_fourth :
    ComputableIn₂ {oracleFunction (OracleJump.zeroJump 4)}
      (fun e v => StageFiniteWager.normalizedWager (UniformStrategyFamily.strategy e) v) :=
  RelativeComputable.transfer stageWager_computableIn (OracleJump.zeroJump_mono (by decide))

end Klr.UniformNormalization
