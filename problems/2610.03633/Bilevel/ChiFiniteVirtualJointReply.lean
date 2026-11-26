import Bilevel.ChiFiniteVirtualUpperReply
import Bilevel.ChiHierarchyExecution

/-! A concrete measurable evaluate function for the actual hierarchy
execution. Its inputs are the current query, old/new finite stores, and the
current coin; the public template's frame is irrelevant to its value. -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory
namespace Bilevel.ChiHierarchyExecution
open ChiHierarchyIndex ChiPrefixEvaluation ChiBoundedChain ChiRecursive ChiCarrier
  PrimitiveGeometry ChiExtension PartialLegendre
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (counts : ℕ → ℕ) (J m : ℕ) (M : ChiRecursive.Node E) (D : Geometry E)
  (hM : M.n=counts 0) (hD : ∀ j I,(D j I).n=counts (j+1))
  (c v : ℝ) (hc : 0<c) (hβ : 0<(D J []).width) (hv : 1≤v) (s : ℕ)
  (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ) (dn : ℝ)
  (hR : ∀ i : Fin J,0<R (i.val+1)) (hw : ∀ i : Fin J,0<(D (i.val+1) []).width)
  (h2 : ∀ active : Bool,∀ p : {p : VirtualState M D |
      ValidState M D (finiteMacroCounter counts J) (canonicalCounter counts J) p},∀ z,
    ‖iteratedFDeriv ℝ 2 (statePotential active m M D J (finiteMacroCounter counts J) (canonicalCounter counts J)
      c v s index radialIndex fineIndex rad R dn p.1) z‖≤1/12)

def virtualJointEvaluate (μ L π ν ρ₀ R₀ : ℝ) (b : Normals s)
    (q : FullNormalVariables E (Blocks m E) (Normals s))
    (old new : Store counts J E) (coin : Bool) :
    FullNormalVariables E (Blocks m E) (Normals s) × FullNormalVariables E (Blocks m E) (Normals s) :=
  (virtualUpperEvaluate counts J m M ν D hM hD ρ₀ R₀ s b q old,
   virtualEvaluate counts J m M D hM hD c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw h2
      μ L π q old new coin)

theorem virtualJointEvaluate_eq_original (μ L π ν ρ₀ R₀ : ℝ) (b : Normals s)
    (q : FullNormalVariables E (Blocks m E) (Normals s)) (old new : Store counts J E) (coin : Bool)
    (f : Joint E (Blocks m E) → ℝ) (hf : Differentiable ℝ f)
    (hu : gradient (stateUpperBase m M ν D J ρ₀ R₀ (finiteMacroCounter counts J) (canonicalCounter counts J)
      (finiteVirtualState counts J M D hM hD old)) (ChiUpper.baseProjection q)=gradient f (ChiUpper.baseProjection q))
    (g g₀ : FullNormalVariables E (Blocks m E) (Normals s) → ℝ)
    (hzero : virtualFullGradient false m M D J (finiteMacroCounter counts J) (canonicalCounter counts J)
      c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw (h2 false) μ L
      (finiteVirtualState counts J M D hM hD old,q)=gradient g₀ q)
    (hone : coin=true → virtualFullGradient true m M D J (finiteMacroCounter counts J) (canonicalCounter counts J)
      c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw (h2 true) μ L
      (finiteVirtualState counts J M D hM hD new,q)=gradient g q) :
    virtualJointEvaluate counts J m M D hM hD c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw h2
      μ L π ν ρ₀ R₀ b q old new coin=
      (gradient (ChiUpper.fullUpper f b) q,ChiConservative.sampleGradient g g₀ π coin q) := by
  unfold virtualJointEvaluate
  rw [virtualUpperEvaluate_eq_original counts J m M ν D hM hD ρ₀ R₀ s b q old f hf hu,
    virtualEvaluate_eq_original counts J m M D hM hD c v hc hβ hv s index radialIndex fineIndex rad R dn
      hR hw h2 μ L π q old new coin g g₀ hzero hone]

theorem virtualJointEvaluate_reframe (UM : Space M.n →ₗᵢ[ℝ] E)
    (U : ∀ j I,Space (D j I).n →ₗᵢ[ℝ] E)
    (h2U : ∀ active : Bool,∀ p : {p : VirtualState M D |
        ValidState M D (finiteMacroCounter counts J) (canonicalCounter counts J) p},∀ z,
      ‖iteratedFDeriv ℝ 2 (statePotential active m (reframeNode M UM) (reframeGeometry D U) J
        (finiteMacroCounter counts J) (canonicalCounter counts J) c v s index radialIndex fineIndex rad R dn p.1) z‖≤1/12)
    (μ L π ν ρ₀ R₀ : ℝ) (b : Normals s)
    (q : FullNormalVariables E (Blocks m E) (Normals s)) (old new : Store counts J E) (coin : Bool) :
    virtualJointEvaluate counts J m (reframeNode M UM) (reframeGeometry D U) hM hD c v hc hβ hv s
      index radialIndex fineIndex rad R dn hR hw h2U μ L π ν ρ₀ R₀ b q old new coin=
    virtualJointEvaluate counts J m M D hM hD c v hc hβ hv s
      index radialIndex fineIndex rad R dn hR hw h2 μ L π ν ρ₀ R₀ b q old new coin := by
  unfold virtualJointEvaluate
  rw [virtualUpperEvaluate_reframe counts J m M ν D hM hD ρ₀ R₀ s UM U b q old,
    virtualEvaluate_reframe counts J m M D hM hD c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw
      h2 UM U h2U μ L π q old new coin]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace (Joint E (Blocks m E))] [BorelSpace (Joint E (Blocks m E))]
  [MeasurableSpace (Joint (Blocks m E) (Normals s))] [BorelSpace (Joint (Blocks m E) (Normals s))]
  [MeasurableSpace (Joint E (Joint (Blocks m E) (Normals s)))]
  [BorelSpace (Joint E (Joint (Blocks m E) (Normals s)))]
  [MeasurableSpace (FullNormalVariables E (Blocks m E) (Normals s))]
  [BorelSpace (FullNormalVariables E (Blocks m E) (Normals s))]

theorem virtualJointEvaluate_measurable (μ L π ν ρ₀ R₀ : ℝ) (b : Normals s) :
    Measurable (fun p : FullNormalVariables E (Blocks m E) (Normals s) ×
      (Store counts J E × (Store counts J E × Bool)) =>
      virtualJointEvaluate counts J m M D hM hD c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw h2
        μ L π ν ρ₀ R₀ b p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let Q := FullNormalVariables E (Blocks m E) (Normals s)
  let Input := Q × (Store counts J E × (Store counts J E × Bool))
  have hu := (virtualUpperEvaluate_measurable counts J m M ν D hM hD ρ₀ R₀ s b).comp
    ((measurable_fst : Measurable (Prod.fst : Input → Q)).prodMk measurable_snd.fst)
  have hg := virtualEvaluate_measurable counts J m M D hM hD c v hc hβ hv s index radialIndex fineIndex rad R dn
    hR hw h2 μ L π
  exact hu.prodMk hg

end Bilevel.ChiHierarchyExecution


