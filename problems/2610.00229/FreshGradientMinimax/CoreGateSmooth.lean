import FreshGradientMinimax.InverseGaussian
import FreshGradientMinimax.CoreGate

/-! The gate and its square root are smooth on the whole line, including the
flat threshold. Explicit first and second root derivatives match Appendix C. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open Polynomial Real

def weightedGate (a : ℝ) (p : ℝ[X]) (t : ℝ) : ℝ :=
  exp a * (p.eval (2 * t - 1)⁻¹ * inverseGaussian a (2 * t - 1))

theorem weightedGate_contDiff {a : ℝ} (ha : 0 < a) {n : ℕ∞} (p : ℝ[X]) :
    ContDiff ℝ n (weightedGate a p) := by
  exact contDiff_const.mul ((inverseGaussian_polynomial_contDiff ha p).comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const))

theorem weightedGate_hasDerivAt {a : ℝ} (ha : 0 < a) (p : ℝ[X]) (t : ℝ) :
    HasDerivAt (weightedGate a p) (2 * weightedGate a (inverseGaussianNext a p) t) t := by
  have hd := ((inverseGaussian_polynomial_hasDerivAt ha p (2 * t - 1)).comp t
    (((hasDerivAt_id t).const_mul 2).sub_const 1)).const_mul (exp a)
  convert hd using 1
  simp only [weightedGate, mul_one]
  ring

def coreGateRoot (t : ℝ) : ℝ := weightedGate (1 / 2) 1 t
def coreGateRootDeriv (t : ℝ) : ℝ := 2 * (2 * t - 1)⁻¹ ^ 3 * coreGateRoot t
def coreGateRootSecond (t : ℝ) : ℝ :=
  4 * ((2 * t - 1)⁻¹ ^ 6 - 3 * (2 * t - 1)⁻¹ ^ 4) * coreGateRoot t

theorem coreGate_weighted : coreGate = weightedGate 1 1 := by
  funext t
  by_cases ht : t ≤ 1 / 2
  · have hx : 2 * t - 1 ≤ 0 := by linarith
    simp [coreGate_zero ht, weightedGate, inverseGaussian_nonpos _ hx]
  · have hx : ¬2 * t - 1 ≤ 0 := by linarith
    simp only [coreGate, if_neg ht, weightedGate, eval_one, one_mul,
      inverseGaussian, if_neg hx, neg_mul, one_mul]
    rw [← exp_add]
    congr 1

theorem coreGate_contDiff {n : ℕ∞} : ContDiff ℝ n coreGate := by
  rw [coreGate_weighted]
  exact weightedGate_contDiff (by norm_num) _

theorem coreGateRoot_contDiff {n : ℕ∞} : ContDiff ℝ n coreGateRoot :=
  weightedGate_contDiff (by norm_num : (0 : ℝ) < 1 / 2) _

theorem coreGateRoot_nonneg (t : ℝ) : 0 ≤ coreGateRoot t := by
  simp only [coreGateRoot, weightedGate, eval_one, one_mul]
  exact mul_nonneg (exp_pos _).le (inverseGaussian_nonneg _ _)

theorem coreGateRoot_zero {t : ℝ} (ht : t ≤ 1 / 2) : coreGateRoot t = 0 := by
  have hx : 2 * t - 1 ≤ 0 := by linarith
  simp [coreGateRoot, weightedGate, inverseGaussian_nonpos _ hx]

theorem coreGateRoot_active {t : ℝ} (ht : 1 / 2 < t) :
    coreGateRoot t = exp (1 / 2) * exp (-(2 * t - 1)⁻¹ ^ 2 / 2) := by
  have hx : ¬2 * t - 1 ≤ 0 := by linarith
  simp only [coreGateRoot, weightedGate, eval_one, one_mul, inverseGaussian, if_neg hx]
  congr 2
  ring

theorem coreGateRoot_sq (t : ℝ) : coreGateRoot t ^ 2 = coreGate t := by
  by_cases ht : t ≤ 1 / 2
  · rw [coreGateRoot_zero ht, coreGate_zero ht]
    norm_num
  · rw [coreGateRoot_active (lt_of_not_ge ht), coreGate, if_neg ht,
      ← exp_add, sq, ← exp_add]
    congr 1
    ring

theorem coreGateRoot_eq_sqrt (t : ℝ) : coreGateRoot t = sqrt (coreGate t) := by
  rw [← coreGateRoot_sq t, Real.sqrt_sq (coreGateRoot_nonneg t)]

theorem coreGateRootDeriv_weighted : coreGateRootDeriv = weightedGate (1 / 2) (C 2 * X ^ 3) := by
  funext t
  simp only [coreGateRootDeriv, coreGateRoot, weightedGate, eval_mul, eval_C, eval_pow, eval_X, eval_one]
  ring

theorem coreGateRoot_hasDerivAt (t : ℝ) : HasDerivAt coreGateRoot (coreGateRootDeriv t) t := by
  convert weightedGate_hasDerivAt (by norm_num : (0 : ℝ) < 1 / 2) 1 t using 1
  simp only [coreGateRootDeriv, coreGateRoot, weightedGate, inverseGaussianNext,
    derivative_one, eval_sub, eval_mul, eval_C, eval_pow, eval_X, eval_one, eval_zero]
  ring

theorem coreGateRootDeriv_hasDerivAt (t : ℝ) :
    HasDerivAt coreGateRootDeriv (coreGateRootSecond t) t := by
  rw [coreGateRootDeriv_weighted]
  convert weightedGate_hasDerivAt (by norm_num : (0 : ℝ) < 1 / 2) (C 2 * X ^ 3) t using 1
  simp only [weightedGate, inverseGaussianNext, coreGateRootSecond, coreGateRoot,
    derivative_mul, derivative_C, derivative_pow, derivative_X,
    eval_sub, eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_one, eval_zero,
    eval_natCast, Nat.reduceSub, Nat.cast_ofNat]
  ring

theorem coreGateRoot_deriv (t : ℝ) : deriv coreGateRoot t = coreGateRootDeriv t :=
  (coreGateRoot_hasDerivAt t).deriv

theorem coreGateRoot_second (t : ℝ) : deriv (deriv coreGateRoot) t = coreGateRootSecond t := by
  rw [show deriv coreGateRoot = coreGateRootDeriv from funext coreGateRoot_deriv]
  exact (coreGateRootDeriv_hasDerivAt t).deriv

theorem coreGate_hasDerivAt (t : ℝ) :
    HasDerivAt coreGate (2 * coreGateRoot t * coreGateRootDeriv t) t := by
  have he : coreGate = fun t => coreGateRoot t ^ 2 := funext (fun t => (coreGateRoot_sq t).symm)
  rw [he]
  simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using (coreGateRoot_hasDerivAt t).pow 2

end FreshGradientMinimax
