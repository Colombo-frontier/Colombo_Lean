import SphereSmoothingAnnularPolar
import UpperSmoothingGradient
set_option maxHeartbeats 1000000
open MeasureTheory MeasureTheory.Measure Set Metric Function Filter
open scoped NNReal Topology
namespace Task006.SphereSmoothing
noncomputable section

/-- The exact ball-to-sphere derivative integral, proved by comparing the
actual compact-cutoff weak identity with both boundary limits. -/
theorem ball_fderiv_integral_eq_surface {d : ℕ} (hd : 0 < d)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ z in closedBall 0 ρ, fderiv ℝ f z) =
      ρ^(d-1) • sphereRadialMean ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) f ρ := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hleft := radialCutoff_smul_integral_tendsto (ρ := ρ)
    (measurable_fderiv ℝ f).aestronglyMeasurable
    (fun z => norm_fderiv_le_of_lipschitz ℝ hf (x₀ := z))
  have hright := interval_average_tendsto (sphereRadialMean_weighted_continuous ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) hf) ρ
  have heq : (fun ε : ℝ => ∫ z, radialCutoff ρ ε z • fderiv ℝ f z) =ᶠ[𝓝[>] 0]
      (fun ε : ℝ => ε⁻¹ • ∫ r in ρ..ρ+ε, r^(d-1) • sphereRadialMean ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) f r) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    change (∫ z, cutoffWeightedDerivative f ρ ε z) = _
    rw [cutoff_weak_annulus_identity hf hρ hε,annularNormal_integral_polar hd hf hρ hε]
  exact tendsto_nhds_unique hleft (hright.congr' heq.symm)

/-- The translated actual ball-smoothing derivative in unnormalized surface
form. Translation uses the exact fderiv shift theorem, including nonsmooth f. -/
theorem ballSmoothDerivative_eq_surface {d : ℕ} (hd : 0 < d)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {ρ : ℝ} (hρ : 0 < ρ) (x : EuclideanSpace ℝ (Fin d)) :
    Task006.Full.ballSmoothDerivative f ρ x =
      (volume.real (closedBall (0 : EuclideanSpace ℝ (Fin d)) ρ))⁻¹ •
        (ρ^(d-1) • sphereRadialMean ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) (fun z => f (x+z)) ρ) := by
  let g : EuclideanSpace ℝ (Fin d) → ℝ := fun z => f (x+z)
  have hg : LipschitzWith K g := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simpa only [g,add_sub_add_left_eq_sub,dist_eq_norm] using hf.dist_le_mul (x+z) (x+w)
  have heq : Task006.Full.ballSmoothDerivative g ρ 0 = Task006.Full.ballSmoothDerivative f ρ x := by
    unfold Task006.Full.ballSmoothDerivative
    apply integral_congr_ae
    apply ae_of_all
    intro u
    simp only [zero_add,g,fderiv_comp_add_left]
  rw [← heq,Task006.Full.ballSmoothDerivative_ballIntegral g hρ 0,
    ball_fderiv_integral_eq_surface hd hg hρ]

/-- Exact scalar cancellation of sphere area against ball volume. -/
theorem surface_ball_coefficient {d : ℕ} (hd : 0 < d) {ρ V : ℝ} (hρ : 0 < ρ) (hV : 0 < V) :
    (ρ^d*V)⁻¹ * ρ^(d-1) * ((d:ℝ)*V) = (d:ℝ)/ρ := by
  have hp : ρ^d=ρ^(d-1)*ρ := by rw [← pow_succ,Nat.sub_add_cancel hd]
  rw [hp]
  field_simp [hρ.ne',hV.ne',pow_ne_zero (d-1) hρ.ne']
  <;> ring

end
end Task006.SphereSmoothing
