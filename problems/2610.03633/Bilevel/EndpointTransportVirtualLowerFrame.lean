import Bilevel.EndpointTransportVirtualFrameIrrelevance
import Bilevel.EndpointTransportVirtualBorel

/-! The lower Borel evaluator uses only numeric node parameters and
disclosed arrays. Replacing the unused frame fields leaves its entire
prebatch inverse and frozen-batch reply unchanged. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre ChiBoundedChain ChiRecursive ChiPrefixEvaluation ChiExtension
  TransportHierarchy TransportRound
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {J n D s : ℕ} (M : Node E) (G : Geometry (Block D))
  (UM : Space M.n →ₗᵢ[ℝ] E) (U : ∀ j I,Space (G j I).n →ₗᵢ[ℝ] Block D)
  (P : ChiFine.Parameters) (index radialIndex : Fin J → Fin s) (fineIndex : Fin s)
  (ρ R : ℕ → ℝ) (dn : ℝ) (rM : ℕ → ℕ) (r rs : ℕ → ℕ → List ℕ → ℕ)

@[simp] theorem statePhysicalPotential_reframe (data : PhysicalPrefixState M G n) :
    statePhysicalPotential (reframeNode M UM) (reframeGeometry G U) P index radialIndex fineIndex ρ R dn rM r rs data=
      statePhysicalPotential M G P index radialIndex fineIndex ρ R dn rM r rs data := by
  funext x
  exact prefixPhysicalHierarchyExtension_reframe G U (r data.1) (rs data.1)
    data.2.2.1 data.2.2.2.1 data.2.2.2.2 M UM (rM data.1) data.2.1
    P index radialIndex fineIndex ρ R dn x

@[simp] theorem statePhysicalExtension_reframe (data : PhysicalPrefixState M G n) :
    statePhysicalExtension (reframeNode M UM) (reframeGeometry G U) P index radialIndex fineIndex ρ R dn rM r rs data=
      statePhysicalExtension M G P index radialIndex fineIndex ρ R dn rM r rs data := by
  unfold statePhysicalExtension
  rw [statePhysicalPotential_reframe]

@[simp] theorem statePhysicalExtension_gradient_reframe [CompleteSpace E] (data : PhysicalPrefixState M G n) :
    gradient (statePhysicalExtension (reframeNode M UM) (reframeGeometry G U) P index radialIndex fineIndex ρ R dn rM r rs data)=
      gradient (statePhysicalExtension M G P index radialIndex fineIndex ρ R dn rM r rs data) := by
  rw [statePhysicalExtension_reframe]

end Bilevel.EndpointTransportResponse
