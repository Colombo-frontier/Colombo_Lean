import Nonsmooth.PlaneSliceData
import Nonsmooth.OrthogonalCoordinateBounds

set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem scalar_slice_local_polynomial_growth (s g : ℝ → ℝ → ℝ) {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hs : ∀ t x, |s t x| ≤ C * (1 + |t| + |x|))
    (hg : ∀ t x, |g t x| ≤ D * (1 + t ^ 2 + x ^ 2)) (t : ℝ) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ r ∈ Metric.ball t 1, ∀ x,
      |s r x| ≤ J * (1 + |x| ^ 2) ∧ |g r x| ≤ J * (1 + |x| ^ 4) := by
  let T := |t| + 1
  let A := C * (2 + T)
  let B := D * (2 + T ^ 2)
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨max A B, hA.trans (le_max_left _ _), ?_⟩
  intro r hr x
  have hrT : |r| ≤ T := by
    have hd : |r - t| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hr
    have hb := abs_add_le (r - t) t
    rw [sub_add_cancel] at hb
    dsimp only [T]
    linarith
  constructor
  · have hp : 1 + |r| + |x| ≤ (2 + T) * (1 + |x| ^ 2) := by
      nlinarith [sq_nonneg (|x| - 1), mul_nonneg hT (sq_nonneg |x|)]
    have hb := mul_le_mul_of_nonneg_left hp hC
    have hm := mul_le_mul_of_nonneg_right (le_max_left A B) (by positivity : 0 ≤ 1 + |x| ^ 2)
    dsimp only [A] at hm
    nlinarith [hs r x]
  · have hr2 := (sq_le_sq₀ (abs_nonneg r) hT).mpr hrT
    rw [sq_abs] at hr2
    have hp : 1 + r ^ 2 + x ^ 2 ≤ (2 + T ^ 2) * (1 + |x| ^ 4) := by
      nlinarith [sq_nonneg (|x| ^ 2 - 1), sq_abs x,
        mul_nonneg (sq_nonneg T) (pow_nonneg (abs_nonneg x) 4)]
    have hb := mul_le_mul_of_nonneg_left hp hD
    have hm := mul_le_mul_of_nonneg_right (le_max_right A B) (by positivity : 0 ≤ 1 + |x| ^ 4)
    dsimp only [B] at hm
    nlinarith [hg r x]

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem planePoint_norm_sq (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (ho : inner ℝ u v = (0 : ℝ)) (t x : ℝ) : ‖planePoint u v t x‖ ^ 2 = t ^ 2 + x ^ 2 := by
  have hvu : inner ℝ v u = (0 : ℝ) := by rw [real_inner_comm]; exact ho
  simp only [planePoint, norm_add_sq_real, norm_smul, hu, hv, Real.norm_eq_abs,
    mul_one, sq_abs, real_inner_smul_left, real_inner_smul_right, hvu, mul_zero, add_zero]

theorem planePoint_norm_le (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (t x : ℝ) :
    ‖planePoint u v t x‖ ≤ |t| + |x| := by
  simpa only [planePoint, norm_smul, hu, hv, Real.norm_eq_abs, mul_one] using norm_add_le (t • v) (x • u)

theorem bilinear_apply_unit_abs_bound (A : E →L[ℝ] E →L[ℝ] ℝ) (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) : |A u v| ≤ ‖A‖ := by
  have h1 := (A u).le_opNorm v
  have h2 := A.le_opNorm u
  rw [Real.norm_eq_abs, hv, mul_one] at h1
  rw [hu, mul_one] at h2
  exact h1.trans h2

end
end Nonsmooth
