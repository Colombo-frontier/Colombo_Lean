import SampleReuse.FiniteAdmissible
import SecondOrder.ScalarJetAlgebra
import GradientHessian.LocalizedNormDerivatives
import RandomizedFO2003.GradientCalculus

open SecondOrder GradientHessian.LocalizedNormDerivatives
open GradientHessian.SmoothNormCompression RandomizedFO2003.Calculus
open scoped InnerProductSpace

namespace SampleReuse
noncomputable section

variable {d : ℕ}

/-- The appendix's smooth two-hypothesis family, with zero-padding-independent
unit direction. In dimension one this is exactly 4 epsilon sqrt(1+x^2)+z*x. -/
def marginalLoss (ε : ℝ) (v : Point d) (z : ℝ) (x : Point d) : ℝ :=
  4*ε*unitSmoothNorm x+z*⟪v,x⟫_ℝ

theorem marginalLoss_contDiff (ε : ℝ) (v : Point d) (z : ℝ) (n : ℕ∞) :
    ContDiff ℝ n (marginalLoss ε v z) :=
  (contDiff_const.mul (unitSmoothNorm_contDiff n)).add
    (contDiff_const.mul (innerSL ℝ v).contDiff)

theorem marginalLoss_gradient (ε : ℝ) (v : Point d) (z : ℝ) :
    gradient (marginalLoss ε v z) = fun x => (4*ε) • unitCompression x+z • v := by
  funext x
  have hs : HasGradientAt unitSmoothNorm (unitCompression x) x := unitSmoothNorm_hasFDerivAt x
  have hl : HasGradientAt (fun y : Point d => ⟪v,y⟫_ℝ) v x := (innerSL ℝ v).hasFDerivAt
  exact (hasGradientAt_add (hasGradientAt_const_mul hs (4*ε))
    (hasGradientAt_const_mul hl z)).gradient

theorem marginalLoss_hessian (ε : ℝ) (v : Point d) (z : ℝ) (x : Point d) :
    hessian (marginalLoss ε v z) x = (4*ε) • unitCompressionDerivative x := by
  change fderiv ℝ (gradient (marginalLoss ε v z)) x = _
  rw [marginalLoss_gradient]
  exact (((unitCompression_hasFDerivAt x).const_smul (4*ε)).add_const (z • v)).fderiv

theorem marginalLoss_gradient_lipschitz {ε : ℝ} (hε : 0 ≤ ε)
    (v : Point d) (z : ℝ) (x y : Point d) :
    ‖gradient (marginalLoss ε v z) x-gradient (marginalLoss ε v z) y‖ ≤ 4*ε*‖x-y‖ := by
  rw [marginalLoss_gradient]
  simp only [add_sub_add_right_eq_sub,← smul_sub,norm_smul,Real.norm_of_nonneg (by positivity : 0 ≤ 4*ε)]
  exact mul_le_mul_of_nonneg_left (unitCompression_sub_norm x y) (by positivity)

theorem marginalLoss_hessian_lipschitz {ε : ℝ} (hε : 0 ≤ ε)
    (v : Point d) (z : ℝ) (x y : Point d) :
    ‖hessian (marginalLoss ε v z) x-hessian (marginalLoss ε v z) y‖ ≤ 12*ε*‖x-y‖ := by
  rw [marginalLoss_hessian,marginalLoss_hessian,
    ← smul_sub (4*ε) (unitCompressionDerivative x) (unitCompressionDerivative y),
    norm_smul (4*ε) (unitCompressionDerivative x-unitCompressionDerivative y),
    Real.norm_of_nonneg (by positivity : 0 ≤ 4*ε)]
  have hh := mul_le_mul_of_nonneg_left (unitCompressionDerivative_sub_norm x y)
    (by positivity : 0 ≤ 4*ε)
  nlinarith only [hh]

theorem marginalLoss_gradient_error (ε : ℝ) {v : Point d} (hv : ‖v‖=1)
    (z θ : ℝ) (x : Point d) :
    ‖gradient (marginalLoss ε v z) x-gradient (marginalLoss ε v θ) x‖ = |z-θ| := by
  rw [marginalLoss_gradient,marginalLoss_gradient]
  simp only [add_sub_add_left_eq_sub,← sub_smul,norm_smul,hv,mul_one,Real.norm_eq_abs]

theorem marginalLoss_gradient_bound {ε : ℝ} (hε : 0 ≤ ε) {v : Point d} (hv : ‖v‖=1)
    (z : ℝ) (x : Point d) : ‖gradient (marginalLoss ε v z) x‖ ≤ 4*ε+|z| := by
  rw [marginalLoss_gradient]
  apply (norm_add_le _ _).trans
  simp only [norm_smul,hv,mul_one,Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ 4*ε)]
  have hh := mul_le_mul_of_nonneg_left (unitCompression_norm_le_one x) (by positivity : 0 ≤ 4*ε)
  linarith

theorem marginalLoss_nonneg {ε z : ℝ} (hε : 0 ≤ ε) {v : Point d} (hv : ‖v‖=1)
    (hz : |z| ≤ 2*ε) (x : Point d) : 0 ≤ marginalLoss ε v z x := by
  have hi := abs_real_inner_le_norm v x
  rw [hv,one_mul] at hi
  have hs : ‖x‖ ≤ unitSmoothNorm x := by
    have hh := Real.sqrt_le_sqrt (show ‖x‖^2 ≤ 1+‖x‖^2 by linarith)
    simpa only [Real.sqrt_sq (norm_nonneg x)] using hh
  have hp := mul_le_mul_of_nonneg_left hi (abs_nonneg z)
  have hz' := mul_le_mul_of_nonneg_right hz (norm_nonneg x)
  have hl := neg_abs_le (z*⟪v,x⟫_ℝ)
  rw [abs_mul] at hl
  have hs' := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 4*ε)
  unfold marginalLoss
  nlinarith only [hl,hp,hz',hs',mul_nonneg hε (norm_nonneg x)]

theorem marginalLoss_initial_gap {ε z : ℝ} (hε : 0 ≤ ε) {v : Point d} (hv : ‖v‖=1)
    (hz : |z| ≤ 2*ε) (x : Point d) : marginalLoss ε v z 0-marginalLoss ε v z x ≤ 4*ε := by
  have hz0 : marginalLoss ε v z 0 = 4*ε := by
    simp [marginalLoss,unitSmoothNorm]
  rw [hz0]
  linarith [marginalLoss_nonneg hε hv hz x]

theorem marginal_positive_stationary_negative {ε : ℝ} (hε : 0 < ε)
    {v : Point d} (hv : ‖v‖=1) {x : Point d}
    (hs : ‖gradient (marginalLoss ε v (2*ε)) x‖ ≤ ε) : ⟪v,x⟫_ℝ < 0 := by
  by_contra hn
  have hix : 0 ≤ ⟪v,x⟫_ℝ := le_of_not_gt hn
  have hi := real_inner_le_norm (gradient (marginalLoss ε v (2*ε)) x) v
  rw [hv,mul_one] at hi
  rw [marginalLoss_gradient,inner_add_left,real_inner_smul_left,real_inner_smul_left,
    real_inner_self_eq_norm_sq,hv,one_pow,mul_one] at hi
  have hxv : 0 ≤ ⟪unitCompression x,v⟫_ℝ := by
    rw [unitCompression,real_inner_smul_left]
    exact mul_nonneg (compressionFactor_pos x).le (by rwa [real_inner_comm])
  rw [marginalLoss_gradient] at hs
  nlinarith only [hi,hs,hxv,hε]

end
end SampleReuse
