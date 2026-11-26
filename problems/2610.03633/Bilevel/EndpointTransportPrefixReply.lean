import Bilevel.EndpointTransportPrefixBorel
import Bilevel.EndpointTransportQuadraticReachable

/-! Literal full original-SFO reply for the quadratic transport family.
The upper reply includes the complete nonlinear scalar; the lower reply
uses the original query and one frozen transport batch. No derivative is
queried at an inverse or at a point chosen after the batch answers. -/
noncomputable section
open scoped Topology
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre ChiBoundedChain ChiRecursive ChiCarrier ChiPrefixEvaluation
  TransportRound TransportNetwork TransportHierarchy
set_option autoImplicit false
set_option maxHeartbeats 1200000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem statePrefixQuadraticCore_reframe {n D : ℕ} (Q Q' : Rotations n D)
    (M : Node E) (UM : ChiBoundedChain.Space M.n →ₗᵢ[ℝ] E) (ν : ℝ) (G : Geometry (Block D))
    (UG : ∀ j I,ChiBoundedChain.Space (G j I).n →ₗᵢ[ℝ] Block D)
    (ρ R : ℝ) (rM : ℕ → ℕ) (r : ℕ → Fin (M.n+1) → ℕ) (data : ℕ × QuadraticPrefixData M G n) :
    statePrefixQuadraticCore Q (reframeNode M UM) ν (reframeGeometry G UG) ρ R rM r data=
      statePrefixQuadraticCore Q' M ν G ρ R rM r data := rfl

theorem prefixQuadraticUpperGradient_reframe {n D : ℕ} (Q Q' : Rotations n D)
    (M : Node E) (UM : ChiBoundedChain.Space M.n →ₗᵢ[ℝ] E) (ν : ℝ) (G : Geometry (Block D))
    (UG : ∀ j I,ChiBoundedChain.Space (G j I).n →ₗᵢ[ℝ] Block D)
    (ρ R : ℝ) (rM : ℕ → ℕ) (r : ℕ → Fin (M.n+1) → ℕ) (data : ℕ × QuadraticPrefixData M G n)
    (w : Joint (Joint E (Block D)) (Physical n D)) :
    prefixQuadraticUpperGradient Q (reframeNode M UM) ν (reframeGeometry G UG) ρ R rM r data w=
      prefixQuadraticUpperGradient Q' M ν G ρ R rM r data w := rfl

theorem prefixQuadraticJointReply_reframe {n D a p : ℕ} (Q Q' : Rotations n D)
    (M : Node E) (UM : ChiBoundedChain.Space M.n →ₗᵢ[ℝ] E) (ν : ℝ) (G : Geometry (Block D))
    (UG : ∀ j I,ChiBoundedChain.Space (G j I).n →ₗᵢ[ℝ] Block D)
    (ρ R : ℝ) (rM : ℕ → ℕ) (r : ℕ → Fin (M.n+1) → ℕ) (δ c : ℝ) (i : Fin p)
    (data : ℕ × QuadraticPrefixData M G n) (w : Joint (Joint E (Block D)) (Physical n D))
    (q : Queries (n+1) D p)
    (y : Fin ((n+1)*(a+p)+(n+1)*(a+p)) → EuclideanGaussian.Space D) :
    prefixQuadraticJointReply Q (reframeNode M UM) ν (reframeGeometry G UG) ρ R rM r δ c i ((data,w),(q,y))=
      prefixQuadraticJointReply Q' M ν G ρ R rM r δ c i ((data,w),(q,y)) := rfl

theorem prefixQuadraticJointReply_eq_actual_of_germ {n D a p : ℕ} (Qpublic : Rotations n D)
    (M : Node E) (ν : ℝ) (G : Geometry (Block D)) (ρ R : ℝ)
    (rM : ℕ → ℕ) (r : ℕ → Fin (M.n+1) → ℕ) (data : ℕ × QuadraticPrefixData M G n)
    (δ c : ℝ) (g : Generators (n+1) D a) (q : Queries (n+1) D p) (z : Latent (n+1) D)
    (i : Fin p) (w : Joint (Joint E (Block D)) (Physical n D))
    (hq : physical (fun v => q v i)=w.snd)
    (he : quadraticCore (physicalRotations z) M ν G ρ R =ᶠ[𝓝 (quadraticUpperProjection n D w)]
      statePrefixQuadraticCore Qpublic M ν G ρ R rM r data) :
    prefixQuadraticJointReply Qpublic M ν G ρ R rM r δ c i ((data,w),(q,batch (augment g q) z))=
      (gradient (quadraticFullCore (physicalRotations z) M ν G ρ R) w,
       gradient (ChiQuadratic.lower (physicalHessian δ (physicalRotations z))
         (endpointCoupling c (physicalRotations z))) w) := by
  apply Prod.ext
  · exact (quadraticFullCore_gradient_eq_of_germ (physicalRotations z) M ν G ρ R _ w he).symm
  · have h := TransportHierarchy.batchLowerGradient_actual δ c g q z i w.fst
    rw [hq] at h
    exact h

end Bilevel.EndpointTransportResponse
