import Geode.JointSupport
import Geode.GeodesicConvex
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Exact proximal first-order support for an arbitrary globally geodesically
convex objective. The distance derivative is proved also on the diagonal;
no differentiability of the objective is assumed. -/

namespace Geode.Lorentz

open Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem hasDerivAt_dist_segment (p z x : Point E) (hne : p ≠ x) :
    HasDerivAt (fun t : ℝ => dist (segment p z t) x)
      (-form E (direction p x) (logMap p z)) 0 := by
  have hne' : (segmentLine p z).point 0 ≠ (GeodesicLine.constant x).point 0 := by
    simpa only [segmentLine_point, segment_zero, GeodesicLine.constant] using hne
  have hd := hasDerivAt_distance_lines (segmentLine p z) (GeodesicLine.constant x) hne'
  have hr : jointG p x (logMap p z) 0 / Real.sinh (dist p x) =
      -form E (direction p x) (logMap p z) := by
    simpa only [logMap_self, form_zero_right, sub_zero] using joint_direction_slope p x z x
  simpa only [segmentLine_point, segment_zero, GeodesicLine.constant,
    segmentLine_velocity_zero, hr] using hd

/-- Squared distance has its exact first variation even when the reference
point coincides with the initial point of the segment. -/
theorem hasDerivAt_dist_sq_segment (p z x : Point E) :
    HasDerivAt (fun t : ℝ => dist (segment p z t) x ^ 2)
      (-2 * form E (logMap p x) (logMap p z)) 0 := by
  by_cases hpx : p = x
  · subst x
    have heq (t : ℝ) : dist (segment p z t) p ^ 2 = t ^ 2 * dist p z ^ 2 := by
      have hd := segment_dist p z t 0
      rw [segment_zero, sub_zero] at hd
      rw [hd, mul_pow, sq_abs]
    convert ((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (dist p z ^ 2) using 1
    · exact funext heq
    · simp
  · have hd := (hasDerivAt_dist_segment p z x hpx).pow 2
    convert hd using 1
    simp only [segment_zero, pow_one, Nat.cast_ofNat, logMap, form_smul_left]
    ring

/-- The derivative of a smooth upper envelope minimized at the left endpoint
of a nontrivial interval is nonnegative. -/
theorem derivative_nonneg_of_min_on_unit_interval {F : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt F d 0) (hmin : ∀ t ∈ Icc (0 : ℝ) 1, F 0 ≤ F t) : 0 ≤ d := by
  have ht : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  apply ge_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin, ht] with t ht0 ht1
  simp only [zero_add, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr (le_of_lt ht0)) (sub_nonneg.mpr (hmin t ⟨ht0.le, ht1.le⟩))

/-- Global minimality of the proximal objective supplies an ordinary global
Riemannian subgradient at the proximal point. Positivity of `a` is only needed
for existence/convergence of proximal points, not for this implication. -/
theorem proximal_isSubgradient {f : Point E → ℝ} (hf : GConvexFunction f)
    (x p : Point E) (a : ℝ)
    (hmin : ∀ y, f p + a * dist p x ^ 2 ≤ f y + a * dist y x ^ 2) :
    IsSubgradient f p ((2 * a) • logMap p x) := by
  constructor
  · simp only [form_smul_right, logMap_tangent, mul_zero]
  · intro z
    let F : ℝ → ℝ := fun t => f p + t * (f z - f p) + a * dist (segment p z t) x ^ 2
    have hd : HasDerivAt F
        ((f z - f p) + a * (-2 * form E (logMap p x) (logMap p z))) 0 := by
      simpa only [one_mul] using
        ((((hasDerivAt_id (0 : ℝ)).mul_const (f z - f p)).const_add (f p)).add
          ((hasDerivAt_dist_sq_segment p z x).const_mul a))
    have hFmin : ∀ t ∈ Icc (0 : ℝ) 1, F 0 ≤ F t := by
      intro t ht
      have hm := hmin (segment p z t)
      have hc := hf p z t ht.1 ht.2
      dsimp only [F]
      rw [segment_zero, zero_mul, add_zero]
      linarith
    have hs := derivative_nonneg_of_min_on_unit_interval hd hFmin
    rw [form_smul_left]
    linarith

end Geode.Lorentz
