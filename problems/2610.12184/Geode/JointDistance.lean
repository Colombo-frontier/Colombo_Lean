import Geode.GeodesicLine
import Geode.JointDistanceAlgebra
import Geode.JointDistanceScalar

/-! Joint distance convexity in the actual hyperboloid, with no geometric
convexity assumption. The zero-distance case is handled by regularization. -/
namespace Geode.Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem hasDerivAt_jointF (A B : GeodesicLine E) (t : ℝ) :
    HasDerivAt (fun s => jointF (A.point s) (B.point s))
      (jointG (A.point t) (B.point t) (A.velocity t) (B.velocity t)) t := by
  have h := (hasDerivAt_form (A.position_deriv t) (B.position_deriv t)).neg
  convert h using 1
  simp only [jointG]
  ring

theorem hasDerivAt_jointG (A B : GeodesicLine E) (t : ℝ) :
    HasDerivAt (fun s => jointG (A.point s) (B.point s) (A.velocity s) (B.velocity s))
      (jointH (A.point t) (B.point t) (A.velocity t) (B.velocity t)) t := by
  have h₁ := hasDerivAt_form (A.velocity_deriv t) (B.position_deriv t)
  have h₂ := hasDerivAt_form (A.position_deriv t) (B.velocity_deriv t)
  convert h₁.neg.sub h₂ using 1
  simp only [jointH, jointF, A.norm_sq, B.norm_sq, form_smul_left, form_smul_right]
  ring

theorem joint_distance_convex_lines (A B : GeodesicLine E) :
    ConvexOn ℝ Set.univ (fun t => dist (A.point t) (B.point t)) := by
  apply Geode.convexOn_arcosh_of_distance_gram
    (fun t => jointF (A.point t) (B.point t))
    (fun t => jointG (A.point t) (B.point t) (A.velocity t) (B.velocity t))
    (fun t => jointH (A.point t) (B.point t) (A.velocity t) (B.velocity t))
    (hasDerivAt_jointF A B) (hasDerivAt_jointG A B)
    (fun t => reverse_cauchy (A.point t) (B.point t))
  · intro t
    exact (joint_distance_algebra (A.point t) (B.point t) (A.tangent t) (B.tangent t)).1
  · intro t
    exact (joint_distance_algebra (A.point t) (B.point t) (A.tangent t) (B.tangent t)).2

/-- The manuscript's joint convexity inequality for arbitrary pairs of
constant-speed geodesic segments in the concrete hyperboloid model. -/
theorem joint_distance_convex (x₀ x₁ y₀ y₁ : Point E) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    dist (segment x₀ x₁ t) (segment y₀ y₁ t) ≤
      (1 - t) * dist x₀ y₀ + t * dist x₁ y₁ := by
  have h := (joint_distance_convex_lines (segmentLine x₀ x₁) (segmentLine y₀ y₁)).2
    (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (show 0 ≤ 1 - t by linarith) ht (show 1 - t + t = 1 by ring)
  simpa only [smul_eq_mul, mul_zero, mul_one, zero_add, segmentLine_point,
    segment_zero, segment_one] using h

end Geode.Lorentz
