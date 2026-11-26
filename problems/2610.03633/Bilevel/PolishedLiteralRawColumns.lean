import Bilevel.PolishedLiteralExactUpperCut
import Bilevel.ChiPrefixReadout
import Bilevel.ChiConservativeScalar

/-! Original full-gradient replies evaluated from raw disclosed column
arrays. The evaluator takes no hidden isometry or future frame columns.
On the actual blind box its full returned gradient pair equals the source
original reply. -/
noncomputable section
set_option maxHeartbeats 1800000
open scoped BigOperators Topology
namespace Bilevel.PolishedLiteral.Parameters
open PrimitiveGeometry ChiBoundedChain ChiPrefixEvaluation RadialWrapper
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
variable (P : Parameters (X:=X) (U:=U))

abbrev MacroColumns := Fin (P.macroNode.n+1) → X
abbrev MicroColumns := Fin (P.macroNode.n+1) → Fin (P.n+1) → U

def rawSelector (r : ℕ) (a : P.MacroColumns) (i : Fin (P.macroNode.n+1)) (x : X) : ℝ :=
  selector P.macroNode.n i (P.macroNode.width⁻¹ • readout P.macroNode.n r P.macroNode.radius a x)

def rawMicro (counts : Fin (P.macroNode.n+1) → ℕ) (b : P.MicroColumns)
    (i : Fin (P.macroNode.n+1)) (u : U) : Space P.n := readout P.n (counts i) P.radius (b i) u

def rawSelectedFlat (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (a : P.MacroColumns) (b : P.MicroColumns)
    (τ : ℝ) (z : Joint X U) : ℝ :=
  ∑ i : Fin (P.macroNode.n+1),P.rawSelector r a i z.fst*flatResidual P.n P.L P.β τ (P.rawMicro counts b i z.snd)

def rawSelectedInactive (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (a : P.MacroColumns) (b : P.MicroColumns)
    (τ : ℝ) (j : ℕ) (z : Joint X U) : ℝ :=
  ∑ i : Fin (P.macroNode.n+1),P.rawSelector r a i z.fst*
    inactivePiece P.n P.J P.L P.β P.δ τ j (P.rawMicro counts b i z.snd)

def rawInactiveLower (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (a : P.MacroColumns) (b : P.MicroColumns)
    (τ : ℝ) (q : FullMeanSpace (X:=X) (U:=U)) : ℝ :=
  PolishedLiteral.lowerBase P.μ P.L q+P.μ/(2*P.L^2)*(P.rawSelectedFlat r counts a b τ (pack q.fst.fst q.snd.fst))^2-
    P.μ/P.L*(∑ j ∈ Finset.range (P.J+1),P.rawSelectedInactive r counts a b τ j (pack q.fst.fst q.snd.fst)*
      PolishedLiteralCompensated.normal (P.w j) q.snd.snd)

def rawSelectedResidual (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (a : P.MacroColumns) (b : P.MicroColumns)
    (z : Joint X U) : ℝ :=
  ∑ i : Fin (P.macroNode.n+1),P.rawSelector r a i z.fst*
    residual P.n P.L P.β (P.rawMicro (P.activeCutCounts r counts) b i z.snd)

def rawSelectedPiece (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (a : P.MacroColumns) (b : P.MicroColumns)
    (j : ℕ) (z : Joint X U) : ℝ :=
  ∑ i : Fin (P.macroNode.n+1),P.rawSelector r a i z.fst*
    piece P.n P.J P.L P.β P.δ j (P.rawMicro (P.activeCutCounts r counts) b i z.snd)

def rawActiveLower (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (a : P.MacroColumns) (b : P.MicroColumns)
    (q : FullMeanSpace (X:=X) (U:=U)) : ℝ :=
  PolishedLiteral.lowerBase P.μ P.L q+P.μ/(2*P.L^2)*(P.rawSelectedResidual r counts a b (pack q.fst.fst q.snd.fst))^2-
    P.μ/P.L*(∑ j ∈ Finset.range (P.J+1),P.rawSelectedPiece r counts a b j (pack q.fst.fst q.snd.fst)*
      PolishedLiteralCompensated.normal (P.w j) q.snd.snd)

def rawRelease (counts : Fin (P.macroNode.n+1) → ℕ) (b : P.MicroColumns)
    (i : Fin (P.macroNode.n+1)) (u : U) : ℝ :=
  releaseGate (P.rawMicro counts b i u (Fin.last P.n)/P.macroNode.width)

def rawExactUpper (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (a : P.MacroColumns) (b : P.MicroColumns)
    (q : FullMeanSpace (X:=X) (U:=U)) : ℝ :=
  closedChain P.macroNode.n P.macroNode.ell P.macroNode.width (fun i => P.rawRelease counts b i q.snd.fst)
    (readout P.macroNode.n r P.macroNode.radius a q.fst.fst)+
    bowl P.macroRadial P.macroNode.radius q.fst.fst+bowl P.ν P.radius q.snd.fst+
    (∑ i : Fin (P.macroNode.n+1),P.rawSelector r a i q.fst.fst*
      microClosedCarrier P.n P.L P.β P.receiver P.ν P.force P.macroNode.width (P.rawMicro counts b i q.snd.fst))+
    P.L*q.snd.snd

def rawReply (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (a : P.MacroColumns) (b : P.MicroColumns)
    (τ p : ℝ) (coin : Bool) (q : FullMeanSpace (X:=X) (U:=U)) :
    FullMeanSpace (X:=X) (U:=U) × FullMeanSpace (X:=X) (U:=U) :=
  (gradient (P.rawExactUpper r counts a b) q,
    BernoulliOracle.sample p (gradient (P.rawInactiveLower r counts a b τ) q)
      (gradient (P.rawActiveLower r counts a b) q-gradient (P.rawInactiveLower r counts a b τ) q) coin)

theorem raw_coordinates_eq (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ)
    (a : P.MacroColumns) (b : P.MicroColumns)
    (ha : ∀ j : Fin (P.macroNode.n+1),j.val<r → a j=P.macroNode.frame (basis j))
    (hb : ∀ (i : Fin (P.macroNode.n+1)) (j : Fin (P.n+1)),j.val<counts i → b i j=P.frames i (basis j)) :
    (∀ x,P.cutMacroCoordinates r x=readout P.macroNode.n r P.macroNode.radius a x) ∧
    (∀ i u,P.cutMicroCoordinates counts i u=P.rawMicro counts b i u) := by
  constructor
  · intro x
    exact (readout_eq_retained P.macroNode.n r P.macroNode.radius a P.macroNode.frame ha x).symm
  · intro i u
    exact (readout_eq_retained P.n (counts i) P.radius (b i) (P.frames i) (hb i) u).symm

theorem rawInactiveLower_eq_cut (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ)
    (a : P.MacroColumns) (b : P.MicroColumns) (τ : ℝ)
    (ha : ∀ j : Fin (P.macroNode.n+1),j.val<r → a j=P.macroNode.frame (basis j))
    (hb : ∀ (i : Fin (P.macroNode.n+1)) (j : Fin (P.n+1)),j.val<counts i → b i j=P.frames i (basis j)) :
    P.inactiveLowerCut r counts τ=P.rawInactiveLower r counts a b τ := by
  obtain ⟨hm,hu⟩ := P.raw_coordinates_eq r counts a b ha hb
  funext q
  simp only [inactiveLowerCut,cutSelectedFlat,cutSelectedInactive,cutSelector,rawInactiveLower,
    rawSelectedFlat,rawSelectedInactive,rawSelector,hm,hu,packed_fst,packed_snd]

theorem rawActiveLower_eq_cut (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ)
    (a : P.MacroColumns) (b : P.MicroColumns)
    (ha : ∀ j : Fin (P.macroNode.n+1),j.val<r → a j=P.macroNode.frame (basis j))
    (hb : ∀ (i : Fin (P.macroNode.n+1)) (j : Fin (P.n+1)),j.val<P.activeCutCounts r counts i → b i j=P.frames i (basis j)) :
    P.activeLowerCut r counts=P.rawActiveLower r counts a b := by
  obtain ⟨hm,hu⟩ := P.raw_coordinates_eq r (P.activeCutCounts r counts) a b ha hb
  funext q
  simp only [activeLowerCut,cutSelectedResidual,cutSelectedPiece,cutSelector,rawActiveLower,
    rawSelectedResidual,rawSelectedPiece,rawSelector,hm,hu,packed_fst,packed_snd]

theorem rawExactUpper_eq_cut (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ)
    (a : P.MacroColumns) (b : P.MicroColumns)
    (ha : ∀ j : Fin (P.macroNode.n+1),j.val<r → a j=P.macroNode.frame (basis j))
    (hb : ∀ (i : Fin (P.macroNode.n+1)) (j : Fin (P.n+1)),j.val<counts i → b i j=P.frames i (basis j)) :
    P.exactUpperCut r counts=P.rawExactUpper r counts a b := by
  obtain ⟨hm,hu⟩ := P.raw_coordinates_eq r counts a b ha hb
  funext q
  simp only [exactUpperCut,exactUpperCutBase,cutRelease,cutSelector,rawExactUpper,rawRelease,rawSelector,hm,hu,packed_fst,packed_snd]

/-- Source actual--virtual deterministic reply equality for both original
channels. Every premise is a source scale, blind-coordinate inequality, or
an equality of an already disclosed prefix column. -/
theorem actual_reply_eq_raw (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ)
    (a : P.MacroColumns) (b : P.MicroColumns) (τ p : ℝ) (coin : Bool)
    (hb : 0<P.macroNode.width) (hβ : 0<P.β) (hτ : 0<τ) (hτβ : τ≤P.β/4) (hτb : τ≤P.macroNode.width)
    (hδ : ∀ j,j<P.J → τ≤P.δ j)
    (hcounts : ∀ i : Fin (P.macroNode.n+1),r ≤ i.val → counts i≤P.n)
    (ha : ∀ j : Fin (P.macroNode.n+1),j.val<r → a j=P.macroNode.frame (basis j))
    (hold : ∀ (i : Fin (P.macroNode.n+1)) (j : Fin (P.n+1)),j.val<counts i → b i j=P.frames i (basis j))
    (hnew : coin=true → ∀ (i : Fin (P.macroNode.n+1)) (j : Fin (P.n+1)),j.val<P.activeCutCounts r counts i → b i j=P.frames i (basis j))
    (q : FullMeanSpace (X:=X) (U:=U)) (hq : P.BlindBox r counts τ q) :
    (gradient P.upperJoint q,
      ChiConservative.sampleGradient P.sourceLower (P.inactiveSourceLower τ (P.w P.J)) p coin q)=
      P.rawReply r counts a b τ p coin q := by
  rw [P.exactUpperCut_gradient r counts τ hb hβ hτβ hτb hcounts q hq,
    P.rawExactUpper_eq_cut r counts a b ha hold]
  unfold ChiConservative.sampleGradient rawReply
  cases coin with
  | false =>
    simp only [BernoulliOracle.sample,Bool.false_eq_true,if_false,zero_smul,add_zero]
    rw [P.inactiveLowerCut_gradient r counts τ hb hτ hδ q hq,
      P.rawInactiveLower_eq_cut r counts a b τ ha hold]
  | true =>
    rw [P.activeLowerCut_gradient r counts τ hb hβ hτ hτβ hδ q hq,
      P.rawActiveLower_eq_cut r counts a b ha (hnew rfl),
      P.inactiveLowerCut_gradient r counts τ hb hτ hδ q hq,
      P.rawInactiveLower_eq_cut r counts a b τ ha hold]

end Bilevel.PolishedLiteral.Parameters
