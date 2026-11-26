import SphereSmoothingGradientIdentity
import UpperSmoothingInstance
open MeasureTheory MeasureTheory.Measure Set Metric Function Filter
open scoped NNReal Topology
namespace Task006.SphereSmoothing
noncomputable section

theorem toDual_symm_innerSL {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (u : E) : (InnerProductSpace.toDual ℝ E).symm (innerSL ℝ u)=u := by
  apply (InnerProductSpace.toDual ℝ E).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext v
  rfl

/-- Riesz identification commutes with the actual vector integral, including
its original scalar coefficient. No expectation identity is assumed. -/
theorem riesz_integral_innerSL {X E : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (a : X → ℝ) (v : X → E) :
    (InnerProductSpace.toDual ℝ E).symm (∫ x, a x • innerSL ℝ (v x) ∂μ) =
      ∫ x, a x • v x ∂μ := by
  have hc := (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.integral_comp_comm
    (μ := μ) (fun x => a x • innerSL ℝ (v x))
  calc
    _ = ∫ x, (InnerProductSpace.toDual ℝ E).symm (a x • innerSL ℝ (v x)) ∂μ := hc.symm
    _ = _ := by
      apply integral_congr_ae
      apply ae_of_all
      intro x
      simp only [map_smul,toDual_symm_innerSL]

/-- The actual smoothed gradient as an unnormalized sphere integral. -/
theorem ballSmoothGradient_eq_surface {d : ℕ} (hd : 0 < d)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {ρ : ℝ} (hρ : 0 < ρ) (x : EuclideanSpace ℝ (Fin d)) :
    Task006.Full.ballSmoothGradient f ρ x =
      (volume.real (closedBall (0 : EuclideanSpace ℝ (Fin d)) ρ))⁻¹ •
        (ρ^(d-1) • ∫ u : UnitSphere d, f (x+ρ • u.val) • u.val
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) := by
  unfold Task006.Full.ballSmoothGradient
  rw [ballSmoothDerivative_eq_surface hd hf hρ x,map_smul,map_smul]
  exact congrArg (fun w => (volume.real (closedBall (0 : EuclideanSpace ℝ (Fin d)) ρ))⁻¹ • (ρ^(d-1) • w))
    (riesz_integral_innerSL (fun u : UnitSphere d => f (x+ρ • u.val)) (fun u => u.val))

end
end Task006.SphereSmoothing
