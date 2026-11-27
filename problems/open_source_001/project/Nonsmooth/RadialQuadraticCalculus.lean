import Nonsmooth.SoftVectorPotentialCalculus

set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def radialQuadratic (a : ℝ) (b : E) (c : ℝ) (x : E) : ℝ :=
  a * ‖x‖ ^ 2 + inner ℝ b x + c

def radialQuadraticScore (a : ℝ) (b : E) (x : E) : E →L[ℝ] ℝ :=
  (2 * a) • realInnerBilinear x + innerSL ℝ b

theorem radialQuadratic_contDiff (a : ℝ) (b : E) (c : ℝ) :
    ContDiff ℝ 2 (radialQuadratic a b c) :=
  ((contDiff_const.mul (contDiff_norm_sq ℝ)).add (innerSL ℝ b).contDiff).add contDiff_const

theorem radialQuadratic_hasFDerivAt (a : ℝ) (b : E) (c : ℝ) (x : E) :
    HasFDerivAt (radialQuadratic a b c) (radialQuadraticScore a b x) x := by
  convert! (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul a).add
    (innerSL ℝ b).hasFDerivAt).add_const c using 1
  ext v
  simp only [radialQuadraticScore, realInnerBilinear,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem radialQuadraticScore_hasFDerivAt (a : ℝ) (b : E) (x : E) :
    HasFDerivAt (radialQuadraticScore a b) ((2 * a) • realInnerBilinear (E := E)) x :=
  (realInnerBilinear.hasFDerivAt.const_smul (2 * a)).add_const (innerSL ℝ b)

theorem radialQuadratic_hessian_symmetric (a : ℝ) (v w : E) :
    ((2 * a) • realInnerBilinear (E := E)) v w =
      ((2 * a) • realInnerBilinear (E := E)) w v := by
  change (2 * a) * inner ℝ v w = (2 * a) * inner ℝ w v
  rw [real_inner_comm v w]

theorem radialQuadratic_hessian_nonnegative {a : ℝ} (ha : 0 ≤ a) (v : E) :
    0 ≤ ((2 * a) • realInnerBilinear (E := E)) v v := by
  change 0 ≤ (2 * a) * inner ℝ v v
  rw [real_inner_self_eq_norm_sq]
  positivity

theorem radialQuadratic_abs_bound (a : ℝ) (b : E) (c : ℝ) (x : E) :
    |radialQuadratic a b c x| ≤ (|a| + ‖b‖ + |c|) * (1 + ‖x‖ ^ 2) := by
  have hi := abs_real_inner_le_norm b x
  have h1 := abs_add_le (a * ‖x‖ ^ 2) (inner ℝ b x : ℝ)
  have h2 := abs_add_le (a * ‖x‖ ^ 2 + inner ℝ b x) c
  rw [abs_mul, abs_of_nonneg (sq_nonneg ‖x‖)] at h1
  have hx : ‖x‖ ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg (‖x‖ - 1)]
  have hm := mul_le_mul_of_nonneg_left hx (norm_nonneg b)
  dsimp only [radialQuadratic]
  nlinarith [abs_nonneg a, mul_nonneg (abs_nonneg c) (sq_nonneg ‖x‖)]

theorem radialQuadratic_smul (r a : ℝ) (b : E) (c : ℝ) (x : E) :
    r * radialQuadratic a b c x = radialQuadratic (r * a) (r • b) (r * c) x := by
  simp only [radialQuadratic, real_inner_smul_left]
  ring

end
end Nonsmooth
