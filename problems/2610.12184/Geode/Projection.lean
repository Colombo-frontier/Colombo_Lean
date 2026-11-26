import Geode.LogMap

/-! Radial projection onto actual hyperbolic closed balls and its comparison
with any point in the ball. No projection inequality is assumed. -/
namespace Geode.Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def projectBall (o : Point E) (R : ℝ) (hR : 0 ≤ R) (y : Point E) : Point E := by
  classical
  exact if h : dist o y ≤ R then y else
    unitGeodesic o (direction o y) (direction_tangent o y)
      (direction_unit o y (by intro he; apply h; simpa [he] using hR)) R

theorem projectBall_mem (o : Point E) {R : ℝ} (hR : 0 ≤ R) (y : Point E) :
    projectBall o R hR y ∈ Metric.closedBall o R := by
  classical
  unfold projectBall
  split_ifs with h
  · simpa only [Metric.mem_closedBall, dist_comm] using h
  · rw [Metric.mem_closedBall, dist_comm]
    have hd := unitGeodesic_dist o (direction o y) (direction_tangent o y)
      (direction_unit o y (by intro he; apply h; simpa [he] using hR)) 0 R
    simpa only [unitGeodesic_zero, zero_sub, abs_neg, abs_of_nonneg hR] using hd.le

theorem cosine_radial_mono {s r d c : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r)
    (hrd : r ≤ d) (hc : c ≤ 1) :
    Real.cosh r * Real.cosh s - Real.sinh r * Real.sinh s * c ≤
      Real.cosh d * Real.cosh s - Real.sinh d * Real.sinh s * c := by
  have hcos : Real.cosh (r - s) ≤ Real.cosh (d - s) := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg (sub_nonneg.mpr hsr), abs_of_nonneg (by linarith : 0 ≤ d - s)]
    linarith
  rw [Real.cosh_sub, Real.cosh_sub] at hcos
  have hdiff : 0 ≤ (Real.sinh d - Real.sinh r) * Real.sinh s :=
    mul_nonneg (sub_nonneg.mpr (Real.sinh_le_sinh.mpr hrd)) (Real.sinh_nonneg_iff.mpr hs)
  nlinarith [mul_nonneg hdiff (sub_nonneg.mpr hc)]

theorem cosh_dist_unitGeodesic (o p : Point E) (u : Ambient E)
    (hu : form E o.val u = 0) (hn : form E u u = 1) (r : ℝ) :
    Real.cosh (dist (unitGeodesic o u hu hn r) p) =
      Real.cosh r * Real.cosh (dist o p) - Real.sinh r * Real.sinh (dist o p) *
        form E u (direction o p) := by
  have huo : form E u o.val = 0 := by rw [form_comm]; exact hu
  have hup : form E u p.val = Real.sinh (dist o p) * form E u (direction o p) := by
    rw [point_decomposition o p]
    simp only [form_add_right, form_smul_right, huo, mul_zero, zero_add]
  rw [cosh_dist]
  change -form E (Real.cosh r • o.val + Real.sinh r • u) p.val = _
  rw [form_add_left, form_smul_left, form_smul_left, hup, cosh_dist]
  ring

/-- Projection does not increase the distance to any point of the ball. -/
theorem projectBall_dist_le (o : Point E) {R : ℝ} (hR : 0 ≤ R) (y p : Point E)
    (hp : dist o p ≤ R) : dist (projectBall o R hR y) p ≤ dist y p := by
  classical
  by_cases h : dist o y ≤ R
  · unfold projectBall
    rw [dif_pos h]
  have hy : o ≠ y := by intro he; apply h; simpa [he] using hR
  by_cases hop : o = p
  · subst p
    have hm := projectBall_mem o hR y
    simp only [Metric.mem_closedBall] at hm
    exact hm.trans (by rw [dist_comm]; exact le_of_lt (lt_of_not_ge h))
  have hc := (direction_pair_bounds o y p hy hop).2
  have hmono := cosine_radial_mono (s := dist o p) (r := R) (d := dist o y)
    dist_nonneg hp (le_of_lt (lt_of_not_ge h)) hc
  have hcos : Real.cosh (dist (projectBall o R hR y) p) ≤ Real.cosh (dist y p) := by
    unfold projectBall
    rw [dif_neg h, cosh_dist_unitGeodesic, cosh_dist y p, hyperbolic_cosine_law o y p]
    exact hmono
  have hdist := Real.cosh_le_cosh.mp hcos
  simpa only [abs_of_nonneg dist_nonneg] using hdist

end Geode.Lorentz
