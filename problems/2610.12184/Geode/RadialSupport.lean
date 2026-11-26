import Geode.LogMap

/-!
# Global radial support on the actual hyperboloid

The log-map contraction and tangent Cauchy inequality imply the ordinary
Riemannian supporting inequality for distance. No convexity or supporting
inequality is assumed here.
-/

namespace Geode.Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem form_direction_logMap (z p : Point E) (hne : z ≠ p) :
    form E (direction z p) (logMap z p) = dist z p := by
  rw [logMap, form_smul_right, direction_unit z p hne, mul_one]

theorem radial_support_of_ne (z p w : Point E) (hne : z ≠ p) :
    dist z p - form E (direction z p) (logMap z w) ≤ dist w p := by
  have ht : form E z.val (logMap z w - logMap z p) = 0 := by
    rw [form_sub_right, logMap_tangent, logMap_tangent, sub_self]
  have hcs := tangent_cauchy_sq z (direction_tangent z p) ht
  rw [direction_unit z p hne, one_mul, form_sub_right,
    form_direction_logMap z p hne] at hcs
  have hs := hcs.trans (logMap_contraction_sq z w p)
  have hd : 0 ≤ dist w p := dist_nonneg
  have habs : |form E (direction z p) (logMap z w) - dist z p| ≤ dist w p := by
    apply (sq_le_sq₀ (abs_nonneg _) hd).mp
    simpa only [sq_abs] using hs
  have hlo := (abs_le.mp habs).1
  linarith

/-- The zero direction at the center also yields a legal support there. -/
theorem radial_support (z p w : Point E) :
    dist z p - form E (direction z p) (logMap z w) ≤ dist w p := by
  by_cases h : z = p
  · subst p
    simp [direction]
    exact Geode.arcosh_nonneg _
  · exact radial_support_of_ne z p w h

theorem radial_support_gradient (z p w : Point E) :
    dist z p + form E (-direction z p) (logMap z w) ≤ dist w p := by
  simpa only [form_neg_left, sub_eq_add_neg] using radial_support z p w

theorem scaled_radial_support (z p w : Point E) {μ : ℝ} (hμ : 0 ≤ μ) :
    μ * dist z p - μ * form E (direction z p) (logMap z w) ≤ μ * dist w p := by
  have h := mul_le_mul_of_nonneg_left (radial_support z p w) hμ
  simpa only [mul_sub] using h

/-- The actual normal inequality yields the radial-source support used in
the contact-realization Lemma of the manuscript. -/
theorem radial_source_support_of_normal (z p w : Point E) (q : Ambient E)
    {μ : ℝ} (hμ : 0 ≤ μ)
    (hnormal : form E (q + μ • direction z p) (logMap z w) ≤ 0) :
    μ * dist z p + form E q (logMap z w) ≤ μ * dist w p := by
  have hs := scaled_radial_support z p w hμ
  rw [form_add_left, form_smul_left] at hnormal
  linarith

end Geode.Lorentz
