import SphereSmoothingPolarBridge
import SphereSmoothingWeakAnnulus
import SphereSmoothingRadialMean
set_option maxHeartbeats 1000000
open MeasureTheory MeasureTheory.Measure Set Metric Function Filter
open scoped NNReal Topology
namespace Task006.SphereSmoothing
noncomputable section

/-- The annular normal simplifies exactly on every positive radius, without
changing the unit-sphere law. -/
theorem annularNormal_on_ray {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (ρ ε r : ℝ)
    (hr : 0 < r) (u : UnitSphere d) :
    annularNormal f ρ ε (r • u.val) =
      (Ioo ρ (ρ+ε)).indicator (fun r => f (r • u.val) • innerSL ℝ u.val) r := by
  have hu : ‖u.val‖=1 := mem_sphere_zero_iff_norm.1 u.property
  have hn : ‖r • u.val‖=r := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,hu,mul_one]
  have hi : innerSL ℝ (r • u.val) = r • innerSL ℝ u.val := by ext v; simp
  have hnormal : ‖r • u.val‖⁻¹ • innerSL ℝ (r • u.val) = innerSL ℝ u.val := by
    rw [hn,hi,smul_smul,inv_mul_cancel₀ hr.ne',one_smul]
  by_cases h : r ∈ Ioo ρ (ρ+ε)
  · have hray : r • u.val ∈ openAnnulus ρ ε := by change ρ < ‖r • u.val‖ ∧ ‖r • u.val‖ < ρ+ε; rwa [hn]
    rw [annularNormal,indicator_of_mem hray,indicator_of_mem h,hnormal]
  · have hray : r • u.val ∉ openAnnulus ρ ε := by change ¬(ρ < ‖r • u.val‖ ∧ ‖r • u.val‖ < ρ+ε); rwa [hn]
    rw [annularNormal,indicator_of_notMem hray,indicator_of_notMem h]

/-- Actual polar annulus integral, now as the ordinary interval integral
needed for the boundary average. -/
theorem annularNormal_integral_polar {d : ℕ} (hd : 0 < d)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) :
    (∫ z, annularNormal f ρ ε z) =
      ∫ r in ρ..ρ+ε, r^(d-1) • sphereRadialMean (((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere)) f r := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hp := polar_real_radius_integral (volume : Measure (EuclideanSpace ℝ (Fin d)))
    (annularNormal_integrable hf hρ hε)
  rw [show Module.finrank ℝ (EuclideanSpace ℝ (Fin d))=d by simp] at hp
  rw [hp]
  have hinner (r : ℝ) (hr : 0 < r) :
      (∫ u : UnitSphere d, annularNormal f ρ ε (r • u.val) ∂((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere)) =
      (Ioo ρ (ρ+ε)).indicator (fun r => sphereRadialMean ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) f r) r := by
    simp_rw [annularNormal_on_ray f ρ ε r hr]
    by_cases h : r ∈ Ioo ρ (ρ+ε)
    · simp only [indicator_of_mem h,sphereRadialMean]
    · simp only [indicator_of_notMem h,integral_zero]
  have hreorder :
      (∫ r in Ioi (0:ℝ), r^(d-1) •
        (∫ u : UnitSphere d, annularNormal f ρ ε (r • u.val) ∂((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere))) =
      ∫ r in Ioi (0:ℝ), (Ioo ρ (ρ+ε)).indicator
        (fun r => r^(d-1) • sphereRadialMean ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) f r) r := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    rw [hinner r hr]
    by_cases h : r ∈ Ioo ρ (ρ+ε)
    · simp only [indicator_of_mem h]
    · simp only [indicator_of_notMem h,smul_zero]
  rw [hreorder,integral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo]
  have hsub : Ioo ρ (ρ+ε) ⊆ Ioi (0:ℝ) := fun r hr => hρ.trans hr.1
  rw [inter_eq_left.2 hsub,intervalIntegral.integral_of_le (by linarith : ρ ≤ ρ+ε),integral_Ioc_eq_integral_Ioo]

end
end Task006.SphereSmoothing
