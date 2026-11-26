import Bilevel.ChiFiniteVirtualReply
import Bilevel.ChiVirtualUpperReply

/-! The deterministic upper reply for a finite disclosed store. It includes
the nonlinear upper base and uses the old store, independently of the coin. -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory
namespace Bilevel.ChiHierarchyExecution
open ChiHierarchyIndex ChiPrefixEvaluation ChiBoundedChain ChiRecursive ChiCarrier
  PrimitiveGeometry ChiExtension PartialLegendre ChiUpper
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (counts : ℕ → ℕ) (J m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry E)
  (hM : M.n=counts 0) (hD : ∀ j I,(D j I).n=counts (j+1)) (ρ R : ℝ) (s : ℕ)

def virtualUpperEvaluate (b : Normals s) (q : FullNormalVariables E (Blocks m E) (Normals s))
    (old : Store counts J E) : FullNormalVariables E (Blocks m E) (Normals s) :=
  virtualUpperGradient m M ν D J ρ R (finiteMacroCounter counts J) (canonicalCounter counts J) s b
    (finiteVirtualState counts J M D hM hD old,q)

theorem virtualUpperEvaluate_eq_original (b : Normals s)
    (q : FullNormalVariables E (Blocks m E) (Normals s)) (old : Store counts J E)
    (f : Joint E (Blocks m E) → ℝ) (hf : Differentiable ℝ f)
    (he : gradient (stateUpperBase m M ν D J ρ R (finiteMacroCounter counts J) (canonicalCounter counts J)
      (finiteVirtualState counts J M D hM hD old)) (baseProjection q)=gradient f (baseProjection q)) :
    virtualUpperEvaluate counts J m M ν D hM hD ρ R s b q old=gradient (fullUpper f b) q :=
  virtualUpperGradient_eq_original m M ν D J ρ R (finiteMacroCounter counts J) (canonicalCounter counts J) s b
    (finiteVirtualState counts J M D hM hD old,q) f hf he

theorem virtualUpperEvaluate_reframe (UM : Space M.n →ₗᵢ[ℝ] E)
    (U : ∀ j I,Space (D j I).n →ₗᵢ[ℝ] E) (b : Normals s)
    (q : FullNormalVariables E (Blocks m E) (Normals s)) (old : Store counts J E) :
    virtualUpperEvaluate counts J m (reframeNode M UM) ν (reframeGeometry D U) hM hD ρ R s b q old=
      virtualUpperEvaluate counts J m M ν D hM hD ρ R s b q old := by
  unfold virtualUpperEvaluate
  rw [finiteVirtualState_reframe,virtualUpperGradient_reframe]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace (Joint E (Blocks m E))] [BorelSpace (Joint E (Blocks m E))]
  [MeasurableSpace (FullNormalVariables E (Blocks m E) (Normals s))]
  [BorelSpace (FullNormalVariables E (Blocks m E) (Normals s))]

theorem virtualUpperEvaluate_measurable (b : Normals s) :
    Measurable (fun p : FullNormalVariables E (Blocks m E) (Normals s) × Store counts J E =>
      virtualUpperEvaluate counts J m M ν D hM hD ρ R s b p.1 p.2) := by
  let Q := FullNormalVariables E (Blocks m E) (Normals s)
  have hs := (finiteVirtualState_measurable counts J M D hM hD).comp
    (measurable_snd : Measurable (Prod.snd : Q × Store counts J E → Store counts J E))
  have h := (virtualUpperGradient_measurable m M ν D J ρ R (finiteMacroCounter counts J)
    (canonicalCounter counts J) s b).comp (hs.prodMk measurable_fst)
  exact h

end Bilevel.ChiHierarchyExecution
