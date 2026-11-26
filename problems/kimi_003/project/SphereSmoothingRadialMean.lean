import SphereSmoothingBoundaryLimit
open MeasureTheory MeasureTheory.Measure Set Metric Function Filter
open scoped NNReal Topology
namespace Task006.SphereSmoothing
noncomputable section

abbrev UnitSphere (d : ℕ) := sphere (0 : EuclideanSpace ℝ (Fin d)) 1

def sphereRadialMean {d : ℕ} (ν : Measure (UnitSphere d)) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (r : ℝ) : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
  ∫ u : UnitSphere d, f (r • u.val) • innerSL ℝ u.val ∂ν

theorem sphereRadialMean_integrable {d : ℕ} (ν : Measure (UnitSphere d)) [IsFiniteMeasure ν]
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (r : ℝ) :
    Integrable (fun u : UnitSphere d => f (r • u.val) • innerSL ℝ u.val) ν := by
  have hr : Continuous (fun u : UnitSphere d => r • u.val) := continuous_subtype_val.const_smul r
  have hscalar : Continuous (fun u : UnitSphere d => f (r • u.val)) := hf.continuous.comp hr
  have hinner : Continuous (fun u : UnitSphere d => innerSL ℝ u.val) :=
    (innerSL ℝ).continuous.comp continuous_subtype_val
  have hm : Continuous (fun u : UnitSphere d => f (r • u.val) • innerSL ℝ u.val) := hscalar.smul hinner
  apply Integrable.of_bound hm.measurable.aestronglyMeasurable (|f 0|+(K:ℝ)*|r|)
  apply ae_of_all
  intro u
  have hu : ‖u.val‖=1 := mem_sphere_zero_iff_norm.1 u.property
  rw [norm_smul,Real.norm_eq_abs,innerSL_apply_norm,hu,mul_one]
  have hh := hf.norm_sub_le (r • u.val) 0
  simp only [Real.norm_eq_abs,sub_zero,norm_smul,hu,mul_one] at hh
  have ha : |f (r • u.val)| ≤ |f (r • u.val)-f 0|+|f 0| := by
    simpa only [sub_add_cancel] using abs_add_le (f (r • u.val)-f 0) (f 0)
  linarith

theorem sphereRadialMean_lipschitz {d : ℕ} (ν : Measure (UnitSphere d)) [IsFiniteMeasure ν]
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith (Real.toNNReal ((K:ℝ)*ν.real univ)) (sphereRadialMean ν f) := by
  apply LipschitzWith.of_dist_le_mul
  intro r s
  rw [dist_eq_norm,Real.coe_toNNReal _ (mul_nonneg K.coe_nonneg measureReal_nonneg),Real.dist_eq]
  unfold sphereRadialMean
  rw [← integral_sub (sphereRadialMean_integrable ν hf r) (sphereRadialMean_integrable ν hf s)]
  have hb : ∀ᵐ u : UnitSphere d ∂ν,
      ‖f (r • u.val) • innerSL ℝ u.val - f (s • u.val) • innerSL ℝ u.val‖ ≤
        (K:ℝ)*|r-s| := by
    apply ae_of_all
    intro u
    have hu : ‖u.val‖=1 := mem_sphere_zero_iff_norm.1 u.property
    rw [← sub_smul,norm_smul,Real.norm_eq_abs,innerSL_apply_norm,hu,mul_one]
    have hh := hf.norm_sub_le (r • u.val) (s • u.val)
    simpa only [Real.norm_eq_abs,← sub_smul,norm_smul,hu,mul_one] using hh
  have hh := norm_integral_le_of_norm_le_const hb
  convert hh using 1 <;> ring

/-- The radial surface integrand is globally continuous, so the right annulus
average has its actual boundary value as limit. -/
theorem sphereRadialMean_weighted_continuous {d : ℕ} (ν : Measure (UnitSphere d)) [IsFiniteMeasure ν]
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    Continuous (fun r : ℝ => r^(d-1) • sphereRadialMean ν f r) :=
  (continuous_id.pow _).smul (sphereRadialMean_lipschitz ν hf).continuous

end
end Task006.SphereSmoothing
