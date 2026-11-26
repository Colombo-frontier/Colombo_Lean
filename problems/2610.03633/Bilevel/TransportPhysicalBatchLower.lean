import Bilevel.TransportPhysicalBatchHessian

/-! Exact original full quadratic lower-gradient reply from the frozen
transport answers and public endpoint coupling. Neither physical rotations
nor unrevealed columns occur in the evaluated batch reply. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportHierarchy
open EuclideanGaussian TransportNetwork EndpointTransportResponse TransportRound
  PrimitiveGeometry PartialLegendre
set_option maxHeartbeats 800000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def publicEndpointCoupling (n D : ℕ) (c : ℝ) :
    Joint E (Block D) →L[ℝ] Physical n D :=
  endpointCoupling c (fun _ => LinearIsometryEquiv.refl ℝ (Block D))

omit [CompleteSpace E] in
theorem endpointCoupling_public {n D : ℕ} (c : ℝ) (z : Latent (n+1) D) :
    (endpointCoupling c (physicalRotations z) : Joint E (Block D) →L[ℝ] Physical n D)=
      publicEndpointCoupling n D c := by
  ext x i d
  rw [endpointCoupling_apply,physicalRotations_last]
  rfl

def batchLowerGradient {n D m p : ℕ} (δ c : ℝ)
    (q : Queries (n+1) D p) (y : Fin ((n+1)*(m+p)+(n+1)*(m+p)) → Space D)
    (a : Fin p) (x : Joint E (Block D)) : Joint (Joint E (Block D)) (Physical n D) :=
  pack (-(publicEndpointCoupling n D c).adjoint (physical (fun i => q i a)))
    (batchHessian δ q y a-publicEndpointCoupling n D c x)

theorem batchLowerGradient_actual {n D m p : ℕ} (δ c : ℝ)
    (g : Generators (n+1) D m) (q : Queries (n+1) D p) (z : Latent (n+1) D)
    (a : Fin p) (x : Joint E (Block D)) :
    batchLowerGradient δ c q (batch (augment g q) z) a x=
      gradient (ChiQuadratic.lower (physicalHessian δ (physicalRotations z))
        (endpointCoupling c (physicalRotations z))) (pack x (physical (fun i => q i a))) := by
  rw [ChiQuadratic.lower_gradient _ _ (physicalHessian_symmetric δ (physicalRotations z)),
    ChiQuadratic.hessian_apply,endpointCoupling_public]
  unfold batchLowerGradient
  rw [batchHessian_actual]
  rfl

theorem queryPhysical_measurable {n D p : ℕ}
    [MeasurableSpace (Physical n D)] [BorelSpace (Physical n D)] (a : Fin p) :
    Measurable (fun q : Queries (n+1) D p => physical (fun i => q i a)) := by
  apply (PiLp.continuous_equiv_symm 2 (fun _ : EndpointTransportMatrix.Index n => Block D)).measurable.comp
  exact measurable_pi_lambda _ (fun i => (measurable_pi_apply a).comp (measurable_pi_apply i))

theorem batchLowerGradient_measurable {n D m p : ℕ}
    [MeasurableSpace (Joint E (Block D))] [BorelSpace (Joint E (Block D))]
    [MeasurableSpace (Physical n D)] [BorelSpace (Physical n D)]
    [MeasurableSpace (Joint (Joint E (Block D)) (Physical n D))]
    [BorelSpace (Joint (Joint E (Block D)) (Physical n D))]
    (δ c : ℝ) (a : Fin p) :
    Measurable (fun z : Joint E (Block D) ×
      (Queries (n+1) D p × (Fin ((n+1)*(m+p)+(n+1)*(m+p)) → Space D)) =>
      batchLowerGradient δ c z.2.1 z.2.2 a z.1) := by
  let Z := Joint E (Block D) ×
    (Queries (n+1) D p × (Fin ((n+1)*(m+p)+(n+1)*(m+p)) → Space D))
  have hq : Measurable (fun z : Z => z.2.1) := measurable_fst.comp measurable_snd
  have hb : Measurable (fun z : Z => z.2) := measurable_snd
  have hx : Measurable (fun z : Z => z.1) := measurable_fst
  have hY := (queryPhysical_measurable (n:=n) (D:=D) a).comp hq
  have hleft := ((publicEndpointCoupling (E:=E) n D c).adjoint.continuous.measurable.comp hY).neg
  have hright := ((batchHessian_measurable (n:=n) (D:=D) (m:=m) δ a).comp hb).sub
    ((publicEndpointCoupling (E:=E) n D c).continuous.measurable.comp hx)
  exact (packLinear (X:=Joint E (Block D)) (Y:=Physical n D)).continuous.measurable.comp
    (hleft.prodMk hright)

end Bilevel.TransportHierarchy
