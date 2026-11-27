import SphereSmoothingRadialDerivative
open MeasureTheory MeasureTheory.Measure Set Metric Function Filter
open scoped NNReal Topology
namespace Task006.SphereSmoothing
noncomputable section

/-- Explicit normal derivative of the radial cutoff. -/
def radialCutoffDerivative {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ρ ε : ℝ) (z : E) : E →L[ℝ] ℝ :=
  if ρ < ‖z‖ ∧ ‖z‖ < ρ+ε then (-(ε*‖z‖)⁻¹) • innerSL ℝ z else 0

/-- The only exceptional locations are the two zero-volume boundary spheres.
The result includes dimension zero, since both radii are positive. -/
theorem radialCutoff_hasFDerivAt_ae {d : ℕ} {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) :
    ∀ᵐ z : EuclideanSpace ℝ (Fin d),
      HasFDerivAt (radialCutoff (E := EuclideanSpace ℝ (Fin d)) ρ ε)
        (radialCutoffDerivative ρ ε z) z := by
  have hnot (r : ℝ) (hr : r ≠ 0) :
      ∀ᵐ z : EuclideanSpace ℝ (Fin d), ‖z‖ ≠ r := by
    apply ae_iff.2
    simpa only [not_ne_iff, Metric.sphere, dist_zero_right] using
      addHaar_sphere_of_ne_zero (volume : Measure (EuclideanSpace ℝ (Fin d))) (0 : _) hr
  filter_upwards [hnot ρ hρ.ne', hnot (ρ+ε) (by positivity)] with z hz₁ hz₂
  by_cases hzin : ‖z‖ < ρ
  · have hfalse : ¬(ρ < ‖z‖ ∧ ‖z‖ < ρ+ε) := fun ha => (not_lt_of_gt hzin) ha.1
    have hh := radialCutoff_hasFDerivAt_inside (E := EuclideanSpace ℝ (Fin d)) hε hzin
    simpa only [radialCutoffDerivative, if_neg hfalse] using hh
  · by_cases hzout : ‖z‖ < ρ+ε
    · have hlow : ρ < ‖z‖ := lt_of_le_of_ne (le_of_not_gt hzin) (Ne.symm hz₁)
      have hh := radialCutoff_hasFDerivAt_annulus hρ hε hlow hzout
      have htrue : ρ < ‖z‖ ∧ ‖z‖ < ρ+ε := ⟨hlow,hzout⟩
      simpa only [radialCutoffDerivative, if_pos htrue] using hh
    · have hhigh : ρ+ε < ‖z‖ := lt_of_le_of_ne (le_of_not_gt hzout) (Ne.symm hz₂)
      have hh := radialCutoff_hasFDerivAt_outside (E := EuclideanSpace ℝ (Fin d)) hε hhigh
      simpa only [radialCutoffDerivative, if_neg (by tauto : ¬(ρ < ‖z‖ ∧ ‖z‖ < ρ+ε))] using hh

end
end Task006.SphereSmoothing
