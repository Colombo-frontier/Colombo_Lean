import Bilevel.EndpointTransportUpperPrefix
import Bilevel.EndpointTransportVirtualFrameIrrelevance

/-! The full physical upper prefix scalar uses only numerical source fields
and disclosed arrays; its template frames are never evaluated. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry ChiBoundedChain ChiRecursive ChiCarrier ChiPrefixEvaluation
set_option autoImplicit false
set_option maxHeartbeats 400000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem prefixPhysicalUpperBase_reframe {m n D : ℕ} (M : Node E)
    (UM : Space M.n →ₗᵢ[ℝ] E) (ν : ℝ) (G : Geometry (Block D))
    (UG : ∀ j I,Space (G j I).n →ₗᵢ[ℝ] Block D) (J : ℕ) (ρ R : ℝ)
    (rM : ℕ) (r : ℕ → List ℕ → ℕ) (MC : Fin (M.n+1) → E)
    (C : ∀ j I,Fin ((G j I).n+1) → Block D)
    (T : ∀ j I,Fin ((G j I).n+1) → Physical n D) :
    prefixPhysicalUpperBase m (reframeNode M UM) ν (reframeGeometry G UG) J ρ R rM r MC C T=
      prefixPhysicalUpperBase m M ν G J ρ R rM r MC C T := by
  funext x
  have hm : virtualMacroValue (reframeNode M UM) ν rM MC x.fst=virtualMacroValue M ν rM MC x.fst := rfl
  have hr : virtualOuterReleaseCorrection m (reframeNode M UM) (reframeGeometry G UG) rM r MC C
      (baseOrdinaryCoordinates m n D x)=
    virtualOuterReleaseCorrection m M G rM r MC C (baseOrdinaryCoordinates m n D x) := rfl
  simp only [prefixPhysicalUpperBase,hm,hr,virtualOuterSelector_reframe,virtualPhysicalCarrier_reframe]
  rfl

end Bilevel.EndpointTransportResponse
