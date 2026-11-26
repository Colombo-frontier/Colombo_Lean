import Bilevel.EndpointTransportVirtualLowerFrame
import Bilevel.EndpointTransportVirtualUpperReframe

/-! The complete two-gradient evaluator is independent of template frames,
including the total prebatch inverse and the frozen linear correction. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre ChiBoundedChain ChiRecursive ChiCarrier ChiPrefixEvaluation ChiExtension
  TransportHierarchy TransportRound
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem physicalPrefixJointReply_reframe {J n D s a p : ℕ}
    (M : Node E) (UM : Space M.n →ₗᵢ[ℝ] E) (ν : ℝ)
    (G : Geometry (Block D)) (UG : ∀ j I,Space (G j I).n →ₗᵢ[ℝ] Block D)
    (P : ChiFine.Parameters) (index radialIndex : Fin J → Fin s) (fineIndex : Fin s)
    (ρ R : ℕ → ℝ) (dn : ℝ) (b : Normals s)
    (rM : ℕ → ℕ) (r rs : ℕ → ℕ → List ℕ → ℕ) (m δ c₀ cend : ℝ) (i : Fin p) :
    physicalPrefixJointReply (n:=n) (a:=a) (reframeNode M UM) ν (reframeGeometry G UG) P
      index radialIndex fineIndex ρ R dn b rM r rs m δ c₀ cend i=
      physicalPrefixJointReply (n:=n) (a:=a) M ν G P
        index radialIndex fineIndex ρ R dn b rM r rs m δ c₀ cend i := by
  have hu : (fun data : PhysicalPrefixState M G n =>
      gradient (statePhysicalUpper (J:=J) (reframeNode M UM) ν (reframeGeometry G UG) (ρ 0) (R 0) b rM r data))=
      (fun data : PhysicalPrefixState M G n =>
        gradient (statePhysicalUpper (J:=J) M ν G (ρ 0) (R 0) b rM r data)) := by
    funext data w
    exact statePhysicalUpper_gradient_reframe M UM ν G UG (ρ 0) (R 0) b rM r data w
  have hl : (fun data : PhysicalPrefixState M G n =>
      gradient (statePhysicalExtension (reframeNode M UM) (reframeGeometry G UG) P
        index radialIndex fineIndex ρ R dn rM r rs data))=
      (fun data : PhysicalPrefixState M G n =>
        gradient (statePhysicalExtension M G P index radialIndex fineIndex ρ R dn rM r rs data)) := by
    funext data
    exact statePhysicalExtension_gradient_reframe M G UM UG P index radialIndex fineIndex ρ R dn rM r rs data
  unfold physicalPrefixJointReply
  exact congrArg₂ (fun (upper lower : PhysicalPrefixState M G n →
    HybridQuery E (Blocks J (Block D)) (Normals s) n D →
      HybridQuery E (Blocks J (Block D)) (Normals s) n D) =>
        virtualJointReply (a:=a) upper lower m δ c₀ cend i) hu hl

end Bilevel.EndpointTransportResponse
