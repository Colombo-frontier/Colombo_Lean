import Geode.JointDistance
import Geode.Subgradient
import Mathlib.Analysis.Convex.Deriv

/-! Global first-order support for actual hyperbolic distance, deduced from
joint geodesic convexity and the explicit Lorentz derivative. -/
namespace Geode.Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem hasDerivAt_distance_lines (A B : GeodesicLine E) {t : ℝ}
    (hne : A.point t ≠ B.point t) :
    HasDerivAt (fun s => dist (A.point s) (B.point s))
      (jointG (A.point t) (B.point t) (A.velocity t) (B.velocity t) /
        Real.sinh (dist (A.point t) (B.point t))) t := by
  have hF : 1 < jointF (A.point t) (B.point t) := by
    apply lt_of_le_of_ne (reverse_cauchy _ _)
    intro h
    exact hne ((reverse_cauchy_eq_iff _ _).mp h.symm)
  have hsqrt : Real.sqrt (jointF (A.point t) (B.point t) ^ 2 - 1) =
      Real.sinh (dist (A.point t) (B.point t)) :=
    (Geode.sinh_arcosh (jointF (A.point t) (B.point t))).symm
  have hd := (Geode.hasDerivAt_arcosh hF).comp t (hasDerivAt_jointF A B t)
  rw [hsqrt] at hd
  convert hd using 1
  ring

theorem joint_direction_slope (y z w x : Point E) :
    jointG y z (logMap y w) (logMap z x) / Real.sinh (dist y z) =
      -form E (direction y z) (logMap y w) - form E (direction z y) (logMap z x) := by
  have hleft : form E (direction y z) (logMap y w) =
      (Real.sinh (dist y z))⁻¹ * form E (logMap y w) z.val := by
    simp only [direction, form_smul_left, form_sub_left,
      logMap_tangent, mul_zero, sub_zero, form_comm z.val (logMap y w)]
  have hright : form E (direction z y) (logMap z x) =
      (Real.sinh (dist y z))⁻¹ * form E y.val (logMap z x) := by
    simp only [direction, form_smul_left, form_sub_left,
      logMap_tangent, mul_zero, sub_zero, dist_comm z y]
  rw [hleft, hright]
  unfold jointG
  ring

/-- Joint distance support at distinct base points, with the exact two
Riemannian derivatives appearing in the manuscript's contact proof. -/
theorem joint_distance_support (y z w x : Point E) (hne : y ≠ z) :
    dist y z - form E (direction y z) (logMap y w) -
      form E (direction z y) (logMap z x) ≤ dist w x := by
  let A := segmentLine y w
  let B := segmentLine z x
  have hne0 : A.point 0 ≠ B.point 0 := by simpa [A, B] using hne
  have hd := hasDerivAt_distance_lines A B hne0
  have hc := joint_distance_convex_lines A B
  have hs := hc.le_slope_of_hasDerivAt (Set.mem_univ (0 : ℝ))
    (Set.mem_univ (1 : ℝ)) (by norm_num : (0 : ℝ) < 1) hd
  simp only [slope_def_field, A, B, segmentLine_point, segment_zero, segment_one,
    segmentLine_velocity_zero, sub_zero, div_one] at hs
  rw [joint_direction_slope] at hs
  linarith

/-- The distance to a fixed point has its usual unit Riemannian subgradient. -/
theorem distance_isSubgradient (z p : Point E) (hne : z ≠ p) :
    IsSubgradient (fun y => dist y p) z (-direction z p) := by
  constructor
  · simp [direction_tangent]
  · intro y
    have h := joint_distance_support z p y p hne
    simpa only [form_neg_left, logMap_self, form_zero_right, sub_zero, sub_eq_add_neg,
      neg_zero, add_zero] using h

theorem distance_isSubgradient_at_center (p : Point E) :
    IsSubgradient (fun y => dist y p) p 0 := by
  rw [isSubgradient_zero_iff]
  intro y
  simp only [dist_self]
  exact dist_nonneg

theorem distance_source_support (z p x : Point E) (hne : z ≠ p) :
    dist z p - form E (direction z p) (logMap z x) ≤ dist x p := by
  simpa only [form_neg_left, sub_eq_add_neg] using (distance_isSubgradient z p hne).2 x

end Geode.Lorentz
