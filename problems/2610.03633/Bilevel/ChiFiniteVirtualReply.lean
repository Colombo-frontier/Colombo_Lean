import Bilevel.ChiFiniteVirtualState
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

abbrev finiteMacroCounter (counts : ℕ → ℕ) (J q : ℕ) := ChiTreeProgress.counter counts (J+1) q 0 []

variable (counts : ℕ → ℕ) (J m : ℕ) (M : ChiRecursive.Node E) (D : Geometry E)
  (hM : M.n=counts 0) (hD : ∀ j I,(D j I).n=counts (j+1))
  (c v : ℝ) (hc : 0<c) (hβ : 0<(D J []).width) (hv : 1≤v) (s : ℕ)
  (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ) (dn : ℝ)
  (hR : ∀ i : Fin J,0<R (i.val+1)) (hw : ∀ i : Fin J,0<(D (i.val+1) []).width)
  (h2 : ∀ active : Bool,∀ p : {p : VirtualState M D |
      ValidState M D (finiteMacroCounter counts J) (canonicalCounter counts J) p},∀ z,
    ‖iteratedFDeriv ℝ 2 (statePotential active m M D J (finiteMacroCounter counts J) (canonicalCounter counts J)
      c v s index radialIndex fineIndex rad R dn p.1) z‖≤1/12)

def virtualEvaluate (μ L π : ℝ) (q : FullNormalVariables E (Blocks m E) (Normals s))
    (old new : Store counts J E) (coin : Bool) : FullNormalVariables E (Blocks m E) (Normals s) :=
  virtualTwoStoreSample m M D J (finiteMacroCounter counts J) (canonicalCounter counts J)
    c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw h2 μ L π coin
    ((finiteVirtualState counts J M D hM hD old,finiteVirtualState counts J M D hM hD new),q)

theorem virtualEvaluate_eq_original (μ L π : ℝ) (q : FullNormalVariables E (Blocks m E) (Normals s))
    (old new : Store counts J E) (coin : Bool)
    (g g₀ : FullNormalVariables E (Blocks m E) (Normals s) → ℝ)
    (hzero : virtualFullGradient false m M D J (finiteMacroCounter counts J) (canonicalCounter counts J)
      c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw (h2 false) μ L
      (finiteVirtualState counts J M D hM hD old,q)=gradient g₀ q)
    (hone : coin=true → virtualFullGradient true m M D J (finiteMacroCounter counts J) (canonicalCounter counts J)
      c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw (h2 true) μ L
      (finiteVirtualState counts J M D hM hD new,q)=gradient g q) :
    virtualEvaluate counts J m M D hM hD c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw h2 μ L π q old new coin=
      ChiConservative.sampleGradient g g₀ π coin q :=
  virtualTwoStoreSample_eq_original m M D J (finiteMacroCounter counts J) (canonicalCounter counts J)
    c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw h2 μ L π coin _ g g₀ hzero hone

theorem virtualEvaluate_reframe (UM : Space M.n →ₗᵢ[ℝ] E)
    (U : ∀ j I,Space (D j I).n →ₗᵢ[ℝ] E)
    (h2U : ∀ active : Bool,∀ p : {p : VirtualState M D |
        ValidState M D (finiteMacroCounter counts J) (canonicalCounter counts J) p},∀ z,
      ‖iteratedFDeriv ℝ 2 (statePotential active m (reframeNode M UM) (reframeGeometry D U) J
        (finiteMacroCounter counts J) (canonicalCounter counts J) c v s index radialIndex fineIndex rad R dn p.1) z‖≤1/12)
    (μ L π : ℝ) (q : FullNormalVariables E (Blocks m E) (Normals s))
    (old new : Store counts J E) (coin : Bool) :
    virtualEvaluate counts J m (reframeNode M UM) (reframeGeometry D U) hM hD c v hc hβ hv s
      index radialIndex fineIndex rad R dn hR hw h2U μ L π q old new coin=
    virtualEvaluate counts J m M D hM hD c v hc hβ hv s
      index radialIndex fineIndex rad R dn hR hw h2 μ L π q old new coin := by
  unfold virtualEvaluate virtualTwoStoreSample
  simp only [finiteVirtualState_reframe]
  rw [virtualFullGradient_reframe m M D J (finiteMacroCounter counts J) (canonicalCounter counts J)
      c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw false UM U (h2 false) (h2U false) μ L,
    virtualFullGradient_reframe m M D J (finiteMacroCounter counts J) (canonicalCounter counts J)
      c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw true UM U (h2 true) (h2U true) μ L]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace (Joint (Blocks m E) (Normals s))] [BorelSpace (Joint (Blocks m E) (Normals s))]
  [MeasurableSpace (Joint E (Joint (Blocks m E) (Normals s)))]
  [BorelSpace (Joint E (Joint (Blocks m E) (Normals s)))]
  [MeasurableSpace (FullNormalVariables E (Blocks m E) (Normals s))]
  [BorelSpace (FullNormalVariables E (Blocks m E) (Normals s))]

theorem virtualEvaluate_measurable (μ L π : ℝ) :
    Measurable (fun p : FullNormalVariables E (Blocks m E) (Normals s) ×
      (Store counts J E × (Store counts J E × Bool)) =>
      virtualEvaluate counts J m M D hM hD c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw h2
        μ L π p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let Q := FullNormalVariables E (Blocks m E) (Normals s)
  let Input := Q × (Store counts J E × (Store counts J E × Bool))
  have hs := finiteVirtualState_measurable counts J M D hM hD
  have hold := hs.comp (measurable_snd.fst : Measurable (fun p : Input => p.2.1))
  have hnew := hs.comp (measurable_snd.snd.fst : Measurable (fun p : Input => p.2.2.1))
  have hargs : Measurable (fun p : Input =>
      (((finiteVirtualState counts J M D hM hD p.2.1,
          finiteVirtualState counts J M D hM hD p.2.2.1),p.1),p.2.2.2)) :=
    ((hold.prodMk hnew).prodMk measurable_fst).prodMk measurable_snd.snd.snd
  have h := (virtualTwoStoreSample_measurable m M D J (finiteMacroCounter counts J) (canonicalCounter counts J)
    c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw h2 μ L π).comp hargs
  exact h

end Bilevel.ChiHierarchyExecution
