import Bilevel.EndpointTransportVirtualUpperBorel
import Bilevel.EndpointTransportVirtualUpperFrame

/-! Full upper scalar and gradient evaluation are invariant under replacing
the template frames. All disclosed vectors and the public readout stay fixed. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry ChiBoundedChain ChiRecursive ChiCarrier ChiPrefixEvaluation ChiExtension TransportHierarchy
set_option autoImplicit false
set_option maxHeartbeats 600000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {J n D s : ℕ} (M : Node E) (UM : Space M.n →ₗᵢ[ℝ] E) (ν : ℝ)
    (G : Geometry (Block D)) (UG : ∀ j I,Space (G j I).n →ₗᵢ[ℝ] Block D)
    (ρ R : ℝ) (b : Normals s) (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ)
    (data : PhysicalPrefixState M G n)

theorem statePhysicalUpperBase_reframe :
    statePhysicalUpperBase (m:=J) (reframeNode M UM) ν (reframeGeometry G UG) J ρ R rM r data=
      statePhysicalUpperBase (m:=J) M ν G J ρ R rM r data :=
  prefixPhysicalUpperBase_reframe M UM ν G UG J ρ R (rM data.1) (r data.1)
    data.2.1 data.2.2.1 data.2.2.2.2

theorem statePhysicalUpper_reframe :
    statePhysicalUpper (J:=J) (reframeNode M UM) ν (reframeGeometry G UG) ρ R b rM r data=
      statePhysicalUpper (J:=J) M ν G ρ R b rM r data := by
  unfold statePhysicalUpper
  rw [statePhysicalUpperBase_reframe M UM ν G UG ρ R rM r data]

theorem statePhysicalUpper_gradient_reframe [CompleteSpace E]
    (w : HybridQuery E (Blocks J (Block D)) (Normals s) n D) :
    gradient (statePhysicalUpper (reframeNode M UM) ν (reframeGeometry G UG) ρ R b rM r data) w=
      gradient (statePhysicalUpper M ν G ρ R b rM r data) w := by
  rw [statePhysicalUpper_reframe M UM ν G UG ρ R b rM r data]

end Bilevel.EndpointTransportResponse
