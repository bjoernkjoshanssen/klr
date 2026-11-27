module

public import Klr.BlockProduct
public import Klr.StageFiniteProbability
public import Klr.Computability.OracleRecursion

/-!
# Effective cylinder probabilities for escaping affine blocks

If block `k` uses only coordinates at least `k`, every length-`n` cylinder has
already reached its final probability at stage `n`. A finite list of ordinary
affine codes then computes this probability exactly, using the existing
rational finite-stage integration algorithm. Only correspondence of the coded
events with the semantic blocks is required; no matrix representation is
chosen by the computation.
-/

@[expose] public section

namespace Klr.EffectiveBlockProduct

open MeasureTheory RationalComputability _root_.Klr.Computability

local instance : Encodable ℚ := (inferInstance : Primcodable ℚ).toEncodable

/-- A simple explicit modulus of escape of the block supports. -/
def Escapes (B : ℕ → AffineBlock) : Prop :=
  ∀ k q, q ∈ (B k).support → k ≤ q

theorem coordinateCutoff_le (B : ℕ → AffineBlock) (hB : Escapes B) (q : ℕ) :
    BlockProduct.coordinateCutoff B q ≤ q + 1 := by
  classical
  unfold BlockProduct.coordinateCutoff
  split_ifs with h
  · exact Nat.succ_le_succ (hB h.choose q h.choose_spec)
  · exact Nat.zero_le _

theorem cutoff_range_le (B : ℕ → AffineBlock) (hB : Escapes B) (n : ℕ) :
    BlockProduct.cutoff B (Finset.range n) ≤ n := by
  apply Finset.sup_le
  intro q hq
  exact (coordinateCutoff_le B hB q).trans
    (Nat.succ_le_iff.mpr (Finset.mem_range.mp hq))

theorem cylinder_dependsOn (s : List Bool) :
    DependsOn (fun X : Cantor => X ∈ cylinder s) (Finset.range s.length : Set ℕ) := by
  intro X Y hXY
  apply propext
  constructor
  · intro hX i hi
    rw [← hXY i (Finset.mem_range.mpr hi)]
    exact hX i hi
  · intro hY i hi
    rw [hXY i (Finset.mem_range.mpr hi)]
    exact hY i hi

/-- The length of the cylinder itself is a sufficient stabilization stage. -/
theorem law_cylinder_eq_stage (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (hB : Escapes B) (s : List Bool) :
    BlockProduct.law B hdis (cylinder s) = PrefixStage.law B s.length (cylinder s) :=
  BlockProduct.law_apply_eq_stage B hdis (Finset.range s.length) (cylinder s)
    (cylinder_dependsOn s) s.length (cutoff_range_le B hB s.length)

/-- The finite header is explicitly constructed, in reverse chronological order. -/
def header (c : ℕ → AffineCode.Data) : ℕ → List AffineCode.Data
  | 0 => []
  | n + 1 => c n :: header c n

theorem event_header (B : ℕ → AffineBlock) (c : ℕ → AffineCode.Data)
    (hc : ∀ k, AffineCode.event (c k) = (B k).event) (n : ℕ) :
    StageFiniteProbability.event (header c n) = PrefixStage.prefixEvent B n := by
  induction n with
  | zero => simp [header]
  | succ n ih =>
    rw [header, StageFiniteProbability.event_cons, ih, hc, PrefixStage.prefixEvent_succ,
      Set.inter_comm]

theorem law_header (B : ℕ → AffineBlock) (c : ℕ → AffineCode.Data)
    (hc : ∀ k, AffineCode.event (c k) = (B k).event) (n : ℕ) :
    StageFiniteProbability.law (header c n) = PrefixStage.law B n := by
  rw [StageFiniteProbability.law, event_header B c hc, PrefixStage.law_eq_cond]

/-- A generous computable prefix bound covering the header and requested cylinder. -/
def depth (cs : List AffineCode.Data) (s : List Bool) : ℕ :=
  (cs.map AffineCode.width).sum + s.length

theorem length_le_depth (cs : List AffineCode.Data) (s : List Bool) :
    s.length ≤ depth cs s := Nat.le_add_left _ _

theorem width_le_depth (cs : List AffineCode.Data) (s : List Bool)
    (c : AffineCode.Data) (hc : c ∈ cs) : AffineCode.width c ≤ depth cs s := by
  have h := List.single_le_sum (fun x _ => Nat.zero_le x) (AffineCode.width c)
    (List.mem_map.mpr ⟨c, hc, rfl⟩ : AffineCode.width c ∈ cs.map AffineCode.width)
  exact h.trans (Nat.le_add_right _ _)

def prefixTest (s w : List Bool) : Bool :=
  EffectiveScan.boundedAll (fun i => decide (w.getD i false = s.getD i false)) s.length

theorem prefixTest_inputPrefix (s : List Bool) (X : Cantor) (n : ℕ) (hn : s.length ≤ n) :
    prefixTest s (ScanRule.inputPrefix X n) = true ↔ X ∈ cylinder s := by
  rw [prefixTest, EffectiveScan.boundedAll_eq_true]
  simp only [decide_eq_true_eq, mem_cylinder]
  apply forall₂_congr
  intro i hi
  rw [ScanRule.getD_inputPrefix X (hi.trans_le hn)]

/-- An exact rational cylinder probability under a finite affine-code header. -/
def cylinderMass (cs : List AffineCode.Data) (s : List Bool) : ℚ :=
  StageFiniteProbability.probability cs (depth cs s) (prefixTest s)

theorem cylinderMass_eq_measureReal (cs : List AffineCode.Data) (s : List Bool) :
    (cylinderMass cs s : ℝ) = (StageFiniteProbability.law cs).real (cylinder s) := by
  have he : {X : Cantor | prefixTest s (ScanRule.inputPrefix X (depth cs s)) = true} =
      cylinder s := Set.ext fun X => prefixTest_inputPrefix s X _ (length_le_depth cs s)
  rw [cylinderMass, StageFiniteProbability.probability_eq_measureReal cs _
    (fun c hc => width_le_depth cs s c hc), he]

/-- Cylinder masses obtained from the explicitly stabilized finite headers. -/
def mass (c : ℕ → AffineCode.Data) (s : List Bool) : ℚ :=
  cylinderMass (header c s.length) s

theorem mass_eq (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (hB : Escapes B) (c : ℕ → AffineCode.Data)
    (hc : ∀ k, AffineCode.event (c k) = (B k).event) (s : List Bool) :
    (mass c s : ℝ) = (BlockProduct.law B hdis).real (cylinder s) := by
  rw [mass, cylinderMass_eq_measureReal, law_header B c hc]
  exact congrArg ENNReal.toReal (law_cylinder_eq_stage B hdis hB s).symm

theorem computable_depth : Computable₂ depth := by
  have hw : Primrec AffineCode.width := Primrec.fst.comp Primrec.fst
  have hs : Primrec (fun cs : List AffineCode.Data => (cs.map AffineCode.width).sum) :=
    Primrec.list_sum (Primrec.list_map Primrec.id (hw.comp Primrec.snd).to₂)
  exact Primrec.nat_add.to_comp.comp (hs.to_comp.comp Computable.fst)
    (Computable.list_length.comp Computable.snd)

theorem computable_prefixTest : Computable₂ prefixTest := by
  have hw : Computable (fun p : (List Bool × List Bool) × ℕ => p.1.2.getD p.2 false) :=
    (Primrec.list_getD false).to_comp.comp
      (Computable.snd.comp Computable.fst) Computable.snd
  have hs : Computable (fun p : (List Bool × List Bool) × ℕ => p.1.1.getD p.2 false) :=
    (Primrec.list_getD false).to_comp.comp
      (Computable.fst.comp Computable.fst) Computable.snd
  have hp : Computable₂ (fun p : List Bool × List Bool => fun i =>
      decide (p.2.getD i false = p.1.getD i false)) :=
    Primrec.eq.decide.to_comp.comp hw hs
  have hc := (EffectiveScan.computable_boundedAll hp).comp
    (Computable.id.pair (Computable.list_length.comp Computable.fst))
  exact hc.of_eq fun _ => rfl

/-- The finite exact probability is uniformly computable in all its data. -/
theorem computable_cylinderMass : Computable₂ cylinderMass :=
  StageFiniteProbability.computable_probability Computable.fst computable_depth
    (computable_prefixTest.comp (Computable.snd.comp Computable.fst) Computable.snd)

private def decodeData (n : ℕ) : AffineCode.Data := (Encodable.decode n).getD default
private def decodeHeader (n : ℕ) : List AffineCode.Data := (Encodable.decode n).getD []
private def decodeWord (n : ℕ) : List Bool := (Encodable.decode n).getD []

private theorem primrec_decodeData : Primrec decodeData :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const default)

private theorem primrec_decodeHeader : Primrec decodeHeader :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

private theorem primrec_decodeWord : Primrec decodeWord :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

private def consEncoded (n : ℕ) : ℕ :=
  Encodable.encode (decodeData (Nat.unpair n).1 :: decodeHeader (Nat.unpair n).2)

private theorem primrec_consEncoded : Primrec consEncoded :=
  Primrec.encode.comp (Primrec.list_cons.comp
    (primrec_decodeData.comp (Primrec.fst.comp Primrec.unpair))
    (primrec_decodeHeader.comp (Primrec.snd.comp Primrec.unpair)))

/-- Building the finite prefix of an oracle-computable code family uses that oracle. -/
theorem header_recursive {O : Set (ℕ →. ℕ)} {c : ℕ → AffineCode.Data}
    (hc : ComputableIn O c) :
    Nat.RecursiveIn O (fun n => Part.some (Encodable.encode (header c n))) := by
  have hcode : Nat.RecursiveIn O (fun n => Part.some (Encodable.encode (c n))) := by
    simpa [ComputableIn, RecursiveIn] using hc
  have hstage := total_comp hcode (total_primrec
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
  have hprevious := total_primrec (O := O)
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
  have hstep := total_comp (total_primrec primrec_consEncoded) (total_pair hstage hprevious)
  have hrec := total_prec (g := fun _ n old => consEncoded (Nat.pair (Encodable.encode (c n)) old))
    (total_primrec (O := O) (Primrec.const (Encodable.encode ([] : List AffineCode.Data)))) hstep
  have h := total_comp hrec
    (total_pair (total_primrec (Primrec.const 0)) (total_primrec Primrec.id))
  apply h.of_eq
  intro n
  simp only [Nat.unpair_pair, id_eq]
  congr 1
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [header, consEncoded, Nat.unpair_pair, decodeData, decodeHeader,
      Encodable.encodek, Option.getD_some] using
      congrArg (fun old => consEncoded (Nat.pair (Encodable.encode (c n)) old)) ih

theorem header_computableIn {O : Set (ℕ →. ℕ)} {c : ℕ → AffineCode.Data}
    (hc : ComputableIn O c) : ComputableIn O (header c) := by
  simpa [ComputableIn, RecursiveIn] using header_recursive hc

private theorem computableIn_of_total_decode {α β : Type*}
    [Primcodable α] [Primcodable β] [Inhabited α] {O : Set (ℕ →. ℕ)} {f : α → β}
    (hf : Nat.RecursiveIn O (fun n => Part.some
      (Encodable.encode (f ((Encodable.decode n).getD default))))) :
    ComputableIn O f := by
  have hmask : Partrec (fun n : ℕ =>
      (Encodable.decode (α := α) n : Part α).map (fun _ => n)) :=
    (Computable.ofOption (Computable.decode (α := α))).map Computable.fst
  change Nat.RecursiveIn O (fun n => Part.bind (Encodable.decode (α := α) n)
    (fun a => (Part.some (f a)).map Encodable.encode))
  apply (Nat.RecursiveIn.comp hf (RecursiveIn.iff_nat.mp hmask.recursiveIn)).of_eq
  intro n
  cases hd : Encodable.decode (α := α) n <;> simp [hd]

private def numericMass (n : ℕ) : ℕ :=
  Encodable.encode (cylinderMass (decodeHeader (Nat.unpair n).1) (decodeWord (Nat.unpair n).2))

private theorem computable_numericMass : Computable numericMass :=
  Computable.encode.comp (computable_cylinderMass.comp
    (primrec_decodeHeader.to_comp.comp (Computable.fst.comp Primrec.unpair.to_comp))
    (primrec_decodeWord.to_comp.comp (Computable.snd.comp Primrec.unpair.to_comp)))

/-- The exact rational cylinder masses are computable in the code family's oracle. -/
theorem mass_computableIn {O : Set (ℕ →. ℕ)} {c : ℕ → AffineCode.Data}
    (hc : ComputableIn O c) : ComputableIn O (mass c) := by
  apply computableIn_of_total_decode
  have hhead := total_comp (header_recursive hc)
    (total_primrec (Primrec.list_length.comp primrec_decodeWord))
  have hword := total_primrec (O := O) (Primrec.encode.comp primrec_decodeWord)
  have h := total_comp (total_computable computable_numericMass) (total_pair hhead hword)
  exact h.of_eq fun n => by
    simp only [numericMass, Nat.unpair_pair, decodeHeader, decodeWord,
      Encodable.encodek, Option.getD_some, mass]
    rfl

/-- The exact rational values also recover the original extended-nonnegative masses. -/
theorem ofReal_mass_eq (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (hB : Escapes B) (c : ℕ → AffineCode.Data)
    (hc : ∀ k, AffineCode.event (c k) = (B k).event) (s : List Bool) :
    ENNReal.ofReal (mass c s : ℝ) = BlockProduct.law B hdis (cylinder s) := by
  rw [mass_eq B hdis hB c hc]
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

/-- An escaping block family given by oracle-computable finite codes has
uniformly oracle-computable exact rational cylinder probabilities. -/
theorem exists_computable_cylinder_mass {A : Oracle} (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (hB : Escapes B) (c : ℕ → AffineCode.Data)
    (hcomp : ComputableIn {oracleFunction A} c)
    (hc : ∀ k, AffineCode.event (c k) = (B k).event) :
    ∃ q : List Bool → ℚ, ComputableIn {oracleFunction A} q ∧
      ∀ s, ENNReal.ofReal (q s : ℝ) = BlockProduct.law B hdis (cylinder s) :=
  ⟨mass c, mass_computableIn hcomp, ofReal_mass_eq B hdis hB c hc⟩

end Klr.EffectiveBlockProduct
