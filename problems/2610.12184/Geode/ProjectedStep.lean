import Geode.ExpMap
import Geode.Projection
import Geode.DistanceSquaredBound
import Geode.SubgradientBounds

/-! The actual projected-subgradient step and its curvature-controlled
recurrence; neither the exponential nor projection bound is a hypothesis. -/
namespace Geode.Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def projectedStep (o : Point E) (R : ℝ) (hR : 0 ≤ R)
    (α : ℝ) (x : Point E) (g : Ambient E) : Point E :=
  projectBall o R hR (expAt x ((-α) • g))

theorem projectedStep_mem (o : Point E) {R : ℝ} (hR : 0 ≤ R)
    (α : ℝ) (x : Point E) (g : Ambient E) :
    dist o (projectedStep o R hR α x g) ≤ R := by
  simpa only [Metric.mem_closedBall, dist_comm] using
    projectBall_mem o hR (expAt x ((-α) • g))

theorem projected_subgradient_step {f : Point E → ℝ} (o x p : Point E)
    {R L α : ℝ} (hR : 0 < R) (hL : 0 ≤ L) (hα : 0 ≤ α)
    (hx : dist o x ≤ R) (hp : dist o p ≤ R) (hstep : α * L ≤ R)
    (hlip : ∀ a b, |f a - f b| ≤ L * dist a b)
    (g : Ambient E) (hg : IsSubgradient f x g) :
    dist (projectedStep o R hR.le α x g) p ^ 2 ≤ dist x p ^ 2 -
      2 * α * (f x - f p) + Geode.curvatureFactor (3 * R) * α ^ 2 * L ^ 2 := by
  have hv : form E x.val ((-α) • g) = 0 := by simp [hg.1]
  have hgg := subgradient_norm_sq_le hL hlip hg
  have hvsq : form E ((-α) • g) ((-α) • g) ≤ α ^ 2 * L ^ 2 := by
    simp only [form_smul_left, form_smul_right]
    nlinarith [mul_le_mul_of_nonneg_left hgg (sq_nonneg α)]
  have hvnorm : tangentNorm ((-α) • g) ≤ α * L := by
    apply (Real.sqrt_le_left (mul_nonneg hα hL)).mpr
    nlinarith only [hvsq]
  let A := exponentialLine x ((-α) • g) hv
  have hxp : dist x p ≤ 2 * R := by
    have htri := dist_triangle x o p
    rw [dist_comm x o] at htri
    linarith
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, dist (A.point t) p ≤ 3 * R := by
    intro t ht
    have hd := exponentialLine_dist x ((-α) • g) hv t 0
    rw [exponentialLine_zero, sub_zero, abs_of_nonneg ht.1] at hd
    have hlength : dist (A.point t) x ≤ R := by
      change dist ((exponentialLine x ((-α) • g) hv).point t) x ≤ R
      rw [hd]
      have hm := mul_le_mul_of_nonneg_right ht.2 (Real.sqrt_nonneg (form E ((-α) • g) ((-α) • g)))
      change t * tangentNorm ((-α) • g) ≤ 1 * tangentNorm ((-α) • g) at hm
      linarith
    exact (dist_triangle (A.point t) x p).trans (by linarith)
  have htaylor := distance_sq_line_upper A p (by linarith : 0 < 3 * R) hbound
  change dist (expMap x ((-α) • g) hv) p ^ 2 ≤
    dist (A.point 0) p ^ 2 - 2 * form E (logMap (A.point 0) p) (A.velocity 0) +
      Geode.curvatureFactor (3 * R) * A.speedSq at htaylor
  dsimp only [A] at htaylor
  rw [exponentialLine_zero, exponentialLine_velocity_zero, exponentialLine_speedSq,
    form_smul_right, form_comm (logMap x p) g] at htaylor
  have hζ : 0 ≤ Geode.curvatureFactor (3 * R) :=
    le_trans (by norm_num) (Geode.one_le_curvatureFactor (by linarith))
  have hsupport := hg.2 p
  have hgrad := mul_le_mul_of_nonneg_left hsupport hα
  have hnorm := mul_le_mul_of_nonneg_left hvsq hζ
  have hproj := projectBall_dist_le o hR.le (expMap x ((-α) • g) hv) p hp
  have hprojsq := (sq_le_sq₀ dist_nonneg dist_nonneg).mpr hproj
  unfold projectedStep
  rw [expAt_eq_expMap x hv]
  nlinarith only [htaylor, hgrad, hnorm, hprojsq]

end Geode.Lorentz
