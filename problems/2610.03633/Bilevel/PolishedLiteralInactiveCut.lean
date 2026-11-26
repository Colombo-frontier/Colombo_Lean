import Bilevel.PolishedLiteralInactiveFormula
import Bilevel.PolishedLiteralScheduleLocality
import Bilevel.PolishedLiteralLowerStrongConvex

/-! Deterministic virtual cut of the actual inactive lower reply. Every
latent coordinate is replaced by its disclosed prefix. The theorem proves
actual scalar equality locally and hence equality of the full joint
Euclidean gradients, including macro components. -/
noncomputable section
set_option maxHeartbeats 1500000
open scoped BigOperators Topology
open Filter
namespace Bilevel.PolishedLiteral.Parameters
open PrimitiveGeometry ChiBoundedChain ChiPrefixEvaluation ZeroChainPotential
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
variable (P : Parameters (X:=X) (U:=U))

def cutMacroCoordinates (r : ℕ) (x : X) : Space P.macroNode.n :=
  retain P.macroNode.n r (P.macroNode.coordinates x)

def cutMicroCoordinates (counts : Fin (P.macroNode.n+1) → ℕ) (i : Fin (P.macroNode.n+1)) (u : U) : Space P.n :=
  retain P.n (counts i) (P.coordinates i u)

def cutSelector (r : ℕ) (i : Fin (P.macroNode.n+1)) (x : X) : ℝ :=
  selector P.macroNode.n i (P.macroNode.width⁻¹ • P.cutMacroCoordinates r x)

def cutSelectedFlat (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (τ : ℝ) (z : Joint X U) : ℝ :=
  ∑ i : Fin (P.macroNode.n+1),P.cutSelector r i z.fst*
    flatResidual P.n P.L P.β τ (P.cutMicroCoordinates counts i z.snd)

def cutSelectedInactive (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (τ : ℝ) (j : ℕ) (z : Joint X U) : ℝ :=
  ∑ i : Fin (P.macroNode.n+1),P.cutSelector r i z.fst*
    inactivePiece P.n P.J P.L P.β P.δ τ j (P.cutMicroCoordinates counts i z.snd)

def inactiveLowerCut (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (τ : ℝ)
    (q : FullMeanSpace (X:=X) (U:=U)) : ℝ :=
  lowerBase P.μ P.L q+P.μ/(2*P.L^2)*(P.cutSelectedFlat r counts τ (pack q.fst.fst q.snd.fst))^2-
    P.μ/P.L*(∑ j ∈ Finset.range (P.J+1),P.cutSelectedInactive r counts τ j (pack q.fst.fst q.snd.fst)*
      PolishedLiteralCompensated.normal (P.w j) q.snd.snd)

def BlindBox (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (τ : ℝ)
    (q : FullMeanSpace (X:=X) (U:=U)) : Prop :=
  (∀ k : Fin (P.macroNode.n+1),r≤k.val → |P.macroNode.coordinates q.fst.fst k|<P.macroNode.width/4) ∧
  (∀ (i : Fin (P.macroNode.n+1)) (k : Fin (P.n+1)),counts i≤k.val → |P.coordinates i q.snd.fst k|<τ)

omit [CompleteSpace U] in
theorem cutSelector_eq (r : ℕ) (hb : 0<P.macroNode.width) (x : X)
    (hx : ∀ k : Fin (P.macroNode.n+1),r≤k.val → |P.macroNode.coordinates x k|≤P.macroNode.width/4)
    (i : Fin (P.macroNode.n+1)) : wrappedSelector P.macroNode i x=P.cutSelector r i x := by
  have ht := selector_prefix_value P.macroNode.n r i (P.macroNode.width⁻¹ • P.macroNode.coordinates x)
    (fun k hk => ZeroChainResidualScaled.scaled_coordinate_small _ hb _ k (hx k hk))
  simpa only [cutSelector,cutMacroCoordinates,wrappedSelector,map_smul] using ht

theorem cutSelectedFlat_eq (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (τ : ℝ)
    (hb : 0<P.macroNode.width) (hτ : 0<τ) (z : Joint X U)
    (hx : ∀ k : Fin (P.macroNode.n+1),r≤k.val → |P.macroNode.coordinates z.fst k|≤P.macroNode.width/4)
    (hu : ∀ (i : Fin (P.macroNode.n+1)) (k : Fin (P.n+1)),counts i≤k.val → |P.coordinates i z.snd k|≤τ) :
    P.selectedFlatResidual τ z=P.cutSelectedFlat r counts τ z := by
  unfold selectedFlatResidual cutSelectedFlat microFlatResidual
  apply Finset.sum_congr rfl
  intro i _
  rw [P.cutSelector_eq r hb z.fst hx i,flatResidual_prefix_value P.n (counts i) P.L P.β τ hτ
    (P.coordinates i z.snd) (hu i)]
  rfl

theorem cutSelectedInactive_eq (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (τ : ℝ)
    (hb : 0<P.macroNode.width) (hτ : 0<τ) (hδ : ∀ j,j<P.J → τ≤P.δ j)
    (j : ℕ) (z : Joint X U)
    (hx : ∀ k : Fin (P.macroNode.n+1),r≤k.val → |P.macroNode.coordinates z.fst k|≤P.macroNode.width/4)
    (hu : ∀ (i : Fin (P.macroNode.n+1)) (k : Fin (P.n+1)),counts i≤k.val → |P.coordinates i z.snd k|≤τ) :
    P.selectedInactivePiece τ j z=P.cutSelectedInactive r counts τ j z := by
  unfold selectedInactivePiece cutSelectedInactive
  apply Finset.sum_congr rfl
  intro i _
  rw [P.cutSelector_eq r hb z.fst hx i,inactivePiece_prefix_value P.n P.J (counts i) P.L P.β P.δ τ hτ hδ j
    (P.coordinates i z.snd) (hu i)]
  rfl

theorem inactiveLowerCut_value (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (τ : ℝ)
    (hb : 0<P.macroNode.width) (hτ : 0<τ) (hδ : ∀ j,j<P.J → τ≤P.δ j)
    (q : FullMeanSpace (X:=X) (U:=U)) (hq : P.BlindBox r counts τ q) :
    P.inactiveSourceLower τ (P.w P.J) q=P.inactiveLowerCut r counts τ q := by
  rw [P.inactiveSourceLower_selected_formula]
  unfold inactiveLowerCut
  rw [P.cutSelectedFlat_eq r counts τ hb hτ (pack q.fst.fst q.snd.fst)
    (fun k hk => (hq.1 k hk).le) (fun i k hk => (hq.2 i k hk).le)]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  rw [P.cutSelectedInactive_eq r counts τ hb hτ hδ j (pack q.fst.fst q.snd.fst)
    (fun k hk => (hq.1 k hk).le) (fun i k hk => (hq.2 i k hk).le)]

theorem blindBox_isOpen (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (τ : ℝ) :
    IsOpen {z : FullMeanSpace (X:=X) (U:=U) | P.BlindBox r counts τ z} := by
  have hcx : Continuous (fun z : FullMeanSpace (X:=X) (U:=U) => z.fst.fst) :=
    (fstMap (X:=X) (U:=U)).continuous.comp (fstMap (X:=Joint X U) (U:=Joint U ℝ)).continuous
  have hcu : Continuous (fun z : FullMeanSpace (X:=X) (U:=U) => z.snd.fst) :=
    (fstMap (X:=U) (U:=ℝ)).continuous.comp (sndMap (X:=Joint X U) (U:=Joint U ℝ)).continuous
  have hm : IsOpen {z : FullMeanSpace (X:=X) (U:=U) | ∀ k : Fin (P.macroNode.n+1),
      r≤k.val → |P.macroNode.coordinates z.fst.fst k|<P.macroNode.width/4} := by
    simp only [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro k
    apply isOpen_iInter_of_finite
    intro _
    exact isOpen_lt (((EuclideanSpace.proj (𝕜:=ℝ) k).continuous.comp
      (P.macroNode.coordinates_contDiff 3).continuous).comp hcx).abs continuous_const
  have hu : IsOpen {z : FullMeanSpace (X:=X) (U:=U) | ∀ (i : Fin (P.macroNode.n+1)) (k : Fin (P.n+1)),
      counts i≤k.val → |P.coordinates i z.snd.fst k|<τ} := by
    simp only [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro k
    apply isOpen_iInter_of_finite
    intro _
    exact isOpen_lt (((EuclideanSpace.proj (𝕜:=ℝ) k).continuous.comp
      (P.coordinates_contDiff i).continuous).comp hcu).abs continuous_const
  exact hm.inter hu

/-- Exact deterministic inactive full reply equals its disclosed-prefix
cut, under the source's strict blind inequalities. -/
theorem inactiveLowerCut_gradient (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (τ : ℝ)
    (hb : 0<P.macroNode.width) (hτ : 0<τ) (hδ : ∀ j,j<P.J → τ≤P.δ j)
    (q : FullMeanSpace (X:=X) (U:=U)) (hq : P.BlindBox r counts τ q) :
    gradient (P.inactiveSourceLower τ (P.w P.J)) q=gradient (P.inactiveLowerCut r counts τ) q := by
  have hopen := P.blindBox_isOpen r counts τ
  have he : P.inactiveSourceLower τ (P.w P.J)=ᶠ[𝓝 q] P.inactiveLowerCut r counts τ := by
    filter_upwards [hopen.mem_nhds hq] with z hz
    exact P.inactiveLowerCut_value r counts τ hb hτ hδ z hz
  simp only [gradient,he.fderiv_eq]

end Bilevel.PolishedLiteral.Parameters
