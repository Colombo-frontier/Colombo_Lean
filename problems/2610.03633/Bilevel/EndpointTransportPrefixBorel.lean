import Bilevel.EndpointTransportPrefixContinuity
import Bilevel.ChiVirtualFrameIrrelevance
import Bilevel.TransportPhysicalBatchLower

/-! Globally Borel evaluation of the complete depth-zero physical upper
reply and quadratic lower reply from disclosed arrays and ONE frozen
network batch. The upper formula reads neither hidden frames nor rotations. -/
noncomputable section
open MeasureTheory
open scoped Topology
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre ChiBoundedChain ChiRecursive ChiCarrier ChiPrefixEvaluation
  TransportRound TransportNetwork EuclideanGaussian
set_option autoImplicit false
set_option maxHeartbeats 1200000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem prefixQuadraticCore_reframe {n D : ℕ} (Q Q' : Rotations n D)
    (M : Node E) (UM : ChiBoundedChain.Space M.n →ₗᵢ[ℝ] E) (ν : ℝ) (G : Geometry (Block D))
    (UG : ∀ j I,ChiBoundedChain.Space (G j I).n →ₗᵢ[ℝ] Block D)
    (ρ R : ℝ) (rM : ℕ) (r : Fin (M.n+1) → ℕ) (data : QuadraticPrefixData M G n) :
    prefixQuadraticCore Q (reframeNode M UM) ν (reframeGeometry G UG) ρ R rM r data.1 data.2.1 data.2.2 =
      prefixQuadraticCore Q' M ν G ρ R rM r data.1 data.2.1 data.2.2 := rfl

def prefixQuadraticUpper {n D : ℕ} (Q : Rotations n D) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (ρ R : ℝ) (rM : ℕ → ℕ) (r : ℕ → Fin (M.n+1) → ℕ)
    (data : ℕ × QuadraticPrefixData M G n) : Joint (Joint E (Block D)) (Physical n D) → ℝ :=
  statePrefixQuadraticCore Q M ν G ρ R rM r data ∘ quadraticUpperProjection n D

omit [CompleteSpace E] in
theorem prefixQuadraticUpper_continuous {n D : ℕ} (Q : Rotations n D) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (ρ R : ℝ) (rM : ℕ → ℕ) (r : ℕ → Fin (M.n+1) → ℕ) :
    Continuous (fun p : (ℕ × QuadraticPrefixData M G n) × Joint (Joint E (Block D)) (Physical n D) =>
      prefixQuadraticUpper Q M ν G ρ R rM r p.1 p.2) := by
  have hm : Continuous (fun p : (ℕ × QuadraticPrefixData M G n) ×
      Joint (Joint E (Block D)) (Physical n D) => (p.1,quadraticUpperProjection n D p.2)) :=
    continuous_fst.prodMk ((quadraticUpperProjection (E:=E) n D).continuous.comp continuous_snd)
  have h := (statePrefixQuadraticCore_continuous Q M ν G ρ R rM r).comp hm
  convert h using 1

def prefixQuadraticUpperGradient {n D : ℕ} (Q : Rotations n D) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (ρ R : ℝ) (rM : ℕ → ℕ) (r : ℕ → Fin (M.n+1) → ℕ)
    (data : ℕ × QuadraticPrefixData M G n) (w : Joint (Joint E (Block D)) (Physical n D)) :=
  gradient (prefixQuadraticUpper Q M ν G ρ R rM r data) w

theorem prefixQuadraticUpperGradient_eq_actual {n D : ℕ} (Q : Rotations n D) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (ρ R : ℝ) (rM : ℕ → ℕ) (r : ℕ → Fin (M.n+1) → ℕ)
    (data : ℕ × QuadraticPrefixData M G n) (w : Joint (Joint E (Block D)) (Physical n D))
    (he : quadraticCore Q M ν G ρ R =ᶠ[𝓝 (quadraticUpperProjection n D w)]
      statePrefixQuadraticCore Q M ν G ρ R rM r data) :
    prefixQuadraticUpperGradient Q M ν G ρ R rM r data w = gradient (quadraticFullCore Q M ν G ρ R) w :=
  (quadraticFullCore_gradient_eq_of_germ Q M ν G ρ R _ w he).symm

section Measurable
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {n D a p : ℕ}
  [MeasurableSpace (Physical n D)] [BorelSpace (Physical n D)]
  [MeasurableSpace (Joint E (Block D))] [BorelSpace (Joint E (Block D))]
  [MeasurableSpace (Joint (Joint E (Block D)) (Physical n D))]
  [BorelSpace (Joint (Joint E (Block D)) (Physical n D))]

omit [MeasurableSpace (Joint E (Block D))] [BorelSpace (Joint E (Block D))] in
theorem prefixQuadraticUpperGradient_measurable (Q : Rotations n D) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (ρ R : ℝ) (rM : ℕ → ℕ) (r : ℕ → Fin (M.n+1) → ℕ) :
    Measurable (fun q : (ℕ × QuadraticPrefixData M G n) × Joint (Joint E (Block D)) (Physical n D) =>
      prefixQuadraticUpperGradient Q M ν G ρ R rM r q.1 q.2) := by
  letI : SecondCountableTopology (Physical n D) := inferInstance
  letI : BorelSpace (QuadraticPrefixData M G n) := inferInstance
  letI : SecondCountableTopology (QuadraticPrefixData M G n) := inferInstance
  exact ParametricGradient.gradient_measurable (prefixQuadraticUpper Q M ν G ρ R rM r)
    (prefixQuadraticUpper_continuous Q M ν G ρ R rM r)

def prefixQuadraticJointReply (Q : Rotations n D) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (ρ R : ℝ) (rM : ℕ → ℕ) (r : ℕ → Fin (M.n+1) → ℕ)
    (δ c : ℝ) (i : Fin p)
    (z : ((ℕ × QuadraticPrefixData M G n) × Joint (Joint E (Block D)) (Physical n D)) ×
      (Queries (n+1) D p × (Fin ((n+1)*(a+p)+(n+1)*(a+p)) → EuclideanGaussian.Space D))) :=
  (prefixQuadraticUpperGradient Q M ν G ρ R rM r z.1.1 z.1.2,
    TransportHierarchy.batchLowerGradient δ c z.2.1 z.2.2 i z.1.2.fst)

theorem prefixQuadraticJointReply_measurable (Q : Rotations n D) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (ρ R : ℝ) (rM : ℕ → ℕ) (r : ℕ → Fin (M.n+1) → ℕ)
    (δ c : ℝ) (i : Fin p) : Measurable (prefixQuadraticJointReply (a:=a) Q M ν G ρ R rM r δ c i) := by
  have hu := (prefixQuadraticUpperGradient_measurable Q M ν G ρ R rM r).comp
    (measurable_fst : Measurable (fun z :
      ((ℕ × QuadraticPrefixData M G n) × Joint (Joint E (Block D)) (Physical n D)) ×
      (Queries (n+1) D p × (Fin ((n+1)*(a+p)+(n+1)*(a+p)) → EuclideanGaussian.Space D)) => z.1))
  have hw : Measurable (fun z :
      ((ℕ × QuadraticPrefixData M G n) × Joint (Joint E (Block D)) (Physical n D)) ×
      (Queries (n+1) D p × (Fin ((n+1)*(a+p)+(n+1)*(a+p)) → EuclideanGaussian.Space D)) => z.1.2) :=
    measurable_snd.comp measurable_fst
  have hx := (jointFstLinear (A:=Joint E (Block D)) (B:=Physical n D)).continuous.measurable.comp hw
  have hl := (TransportHierarchy.batchLowerGradient_measurable (n:=n) (D:=D) (m:=a) δ c i).comp
    (hx.prodMk measurable_snd)
  exact hu.prodMk hl
end Measurable

end Bilevel.EndpointTransportResponse
