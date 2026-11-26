import Bilevel.ChiVirtualBorelReply
import Bilevel.ChiConservativeScalar

/-! The actual conservative Bernoulli reply assembled from the two Borel
virtual branches, and frame irrelevance of the complete branch reply. -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiExtension PartialLegendre
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

variable (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ)
  (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) (c v : ℝ) (hc : 0<c)
  (hβ : 0<(D J []).width) (hv : 1≤v) (s : ℕ)
  (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ) (dn : ℝ)
  (hR : ∀ i : Fin J,0<R (i.val+1)) (hw : ∀ i : Fin J,0<(D (i.val+1) []).width)

theorem virtualFullGradient_reframe (active : Bool)
    (UM : Space M.n →ₗᵢ[ℝ] E) (U : ∀ j I,Space (D j I).n →ₗᵢ[ℝ] F)
    (h2 : ∀ p : {p : VirtualState M D | ValidState M D rM r p},∀ z,
      ‖iteratedFDeriv ℝ 2 (statePotential active m M D J rM r c v s index radialIndex fineIndex rad R dn p.1) z‖≤1/12)
    (h2U : ∀ p : {p : VirtualState M D | ValidState M D rM r p},∀ z,
      ‖iteratedFDeriv ℝ 2 (statePotential active m (reframeNode M UM) (reframeGeometry D U)
        J rM r c v s index radialIndex fineIndex rad R dn p.1) z‖≤1/12)
    (μ L : ℝ) (p : FullVirtualQuery M D m s) :
    virtualFullGradient active m (reframeNode M UM) (reframeGeometry D U) J rM r c v hc hβ hv s
      index radialIndex fineIndex rad R dn hR hw h2U μ L p=
    virtualFullGradient active m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw h2 μ L p := by
  have hi := congrFun (queryInverse_reframe D U m M UM active J rM r c v hc hβ hv s
    index radialIndex fineIndex rad R dn hR hw h2 h2U) (fullQueryInverseInput p)
  have he := statePotential_reframe D U m M UM active J rM r c v s index radialIndex fineIndex rad R dn p.1
  unfold virtualFullGradient
  dsimp only
  rw [hi,he]
  rfl

variable (h2 : ∀ active : Bool,∀ p : {p : VirtualState M D | ValidState M D rM r p},∀ z,
    ‖iteratedFDeriv ℝ 2 (statePotential active m M D J rM r c v s index radialIndex fineIndex rad R dn p.1) z‖≤1/12)

def virtualSampleGradient (μ L π : ℝ) (coin : Bool) (p : FullVirtualQuery M D m s) :
    FullNormalVariables E (Blocks m F) (Normals s) :=
  let g₀ := virtualFullGradient false m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw (h2 false) μ L p
  let g := virtualFullGradient true m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw (h2 true) μ L p
  BernoulliOracle.sample π g₀ (g-g₀) coin

theorem virtualSampleGradient_eq (μ L π : ℝ) (coin : Bool) (p : FullVirtualQuery M D m s)
    (hp : ValidState M D rM r p.1) :
    let f := fun active => fullExtensionLower
      (statePotential active m M D J rM r c v s index radialIndex fineIndex rad R dn p.1)
      (statePotential_contDiff active m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw p.1 hp)
      ⟨1/12,by norm_num⟩ (h2 active ⟨p.1,hp⟩) (by change (1/12:ℝ)<1;norm_num) μ L
    virtualSampleGradient m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw h2 μ L π coin p=
      ChiConservative.sampleGradient (f true) (f false) π coin p.2 := by
  dsimp only
  unfold virtualSampleGradient ChiConservative.sampleGradient
  rw [virtualFullGradient_eq false m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw (h2 false) μ L p hp,
    virtualFullGradient_eq true m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw (h2 true) μ L p hp]

theorem virtualSampleGradient_reframe
    (UM : Space M.n →ₗᵢ[ℝ] E) (U : ∀ j I,Space (D j I).n →ₗᵢ[ℝ] F)
    (h2U : ∀ active : Bool,∀ p : {p : VirtualState M D | ValidState M D rM r p},∀ z,
      ‖iteratedFDeriv ℝ 2 (statePotential active m (reframeNode M UM) (reframeGeometry D U)
        J rM r c v s index radialIndex fineIndex rad R dn p.1) z‖≤1/12)
    (μ L π : ℝ) (coin : Bool) (p : FullVirtualQuery M D m s) :
    virtualSampleGradient m (reframeNode M UM) (reframeGeometry D U) J rM r c v hc hβ hv s
      index radialIndex fineIndex rad R dn hR hw h2U μ L π coin p=
    virtualSampleGradient m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw h2 μ L π coin p := by
  unfold virtualSampleGradient
  rw [virtualFullGradient_reframe m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw
      false UM U (h2 false) (h2U false) μ L p,
    virtualFullGradient_reframe m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw
      true UM U (h2 true) (h2U true) μ L p]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
  [MeasurableSpace (Joint (Blocks m F) (Normals s))] [BorelSpace (Joint (Blocks m F) (Normals s))]
  [MeasurableSpace (Joint E (Joint (Blocks m F) (Normals s)))]
  [BorelSpace (Joint E (Joint (Blocks m F) (Normals s)))]
  [MeasurableSpace (FullNormalVariables E (Blocks m F) (Normals s))]
  [BorelSpace (FullNormalVariables E (Blocks m F) (Normals s))]

theorem virtualSampleGradient_measurable (μ L π : ℝ) :
    Measurable (fun p : FullVirtualQuery M D m s × Bool =>
      virtualSampleGradient m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw h2 μ L π p.2 p.1) := by
  let Q := FullNormalVariables E (Blocks m F) (Normals s)
  let V := Joint (Blocks m F) (Normals s)
  letI : SecondCountableTopology V := inferInstance
  letI : SecondCountableTopology (Joint E (Blocks m F)) := inferInstance
  letI : SecondCountableTopology Q :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Joint E (Blocks m F)) V).toHomeomorph.secondCountableTopology
  have hzero := (virtualFullGradient_measurable false m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw (h2 false) μ L).comp
    (measurable_fst : Measurable (Prod.fst : FullVirtualQuery M D m s × Bool → FullVirtualQuery M D m s))
  have hone := (virtualFullGradient_measurable true m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw (h2 true) μ L).comp
    (measurable_fst : Measurable (Prod.fst : FullVirtualQuery M D m s × Bool → FullVirtualQuery M D m s))
  have hcoin : Measurable (fun p : FullVirtualQuery M D m s × Bool => if p.2 then π⁻¹ else (0:ℝ)) :=
    (measurable_of_finite (fun b : Bool => if b then π⁻¹ else (0:ℝ))).comp measurable_snd
  exact hzero.add (hcoin.smul (hone.sub hzero))

end Bilevel.ChiPrefixEvaluation
