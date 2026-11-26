import FreshGradientMinimax.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! The concrete polynomial transition in Appendix A.1, with its exact
first two derivatives and sharp bounds on the unit transition interval. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def clipTransition (s : ℝ) : ℝ := 1 + s - s ^ 3 + s ^ 4 / 2
def clipTransitionSlope (s : ℝ) : ℝ := 1 - 3 * s ^ 2 + 2 * s ^ 3
def clipTransitionCurve (s : ℝ) : ℝ := -6 * s + 6 * s ^ 2

theorem clipTransition_derivative (s : ℝ) : HasDerivAt clipTransition (clipTransitionSlope s) s := by
  apply ((((hasDerivAt_const s 1).add (hasDerivAt_id s)).sub ((hasDerivAt_id s).pow 3)).add
    (((hasDerivAt_id s).pow 4).div_const 2)).congr_deriv
  simp only [clipTransitionSlope, mul_one, id_eq]
  ring

theorem clipTransitionSlope_derivative (s : ℝ) :
    HasDerivAt clipTransitionSlope (clipTransitionCurve s) s := by
  apply (((hasDerivAt_const s 1).sub (((hasDerivAt_id s).pow 2).const_mul 3)).add
    (((hasDerivAt_id s).pow 3).const_mul 2)).congr_deriv
  simp only [clipTransitionCurve, mul_one, id_eq]
  ring

theorem clipTransition_bounds {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    1 ≤ clipTransition s ∧ clipTransition s ≤ 3 / 2 := by
  have hs2 : s ^ 2 ≤ 1 := by nlinarith
  have hs3 := mul_le_mul_of_nonneg_left hs2 hs
  have hlo : 1 ≤ clipTransition s := by
    unfold clipTransition
    nlinarith only [hs3, sq_nonneg (s ^ 2)]
  have hhi : 0 ≤ (1 - s) ^ 3 * (1 + s) := mul_nonneg (pow_nonneg (by linarith) _) (by linarith)
  refine ⟨hlo, ?_⟩
  unfold clipTransition
  nlinarith only [hhi]

theorem clipTransitionSlope_bounds {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ clipTransitionSlope s ∧ clipTransitionSlope s ≤ 1 := by
  have hlo : 0 ≤ (1 - s) ^ 2 * (1 + 2 * s) := mul_nonneg (sq_nonneg _) (by linarith)
  have hhi : 0 ≤ s ^ 2 * (3 - 2 * s) := mul_nonneg (sq_nonneg _) (by linarith)
  unfold clipTransitionSlope
  constructor <;> nlinarith only [hlo, hhi]

theorem clipTransitionCurve_bound {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    |clipTransitionCurve s| ≤ 3 / 2 := by
  have hss := mul_le_mul_of_nonneg_left hs1 hs
  rw [abs_le]
  unfold clipTransitionCurve
  constructor <;> nlinarith [sq_nonneg (2 * s - 1)]

theorem clipTransition_endpoints : clipTransition 0 = 1 ∧ clipTransition 1 = 3 / 2 := by
  norm_num [clipTransition]

theorem clipTransitionSlope_endpoints : clipTransitionSlope 0 = 1 ∧ clipTransitionSlope 1 = 0 := by
  norm_num [clipTransitionSlope]

theorem clipTransitionCurve_endpoints : clipTransitionCurve 0 = 0 ∧ clipTransitionCurve 1 = 0 := by
  norm_num [clipTransitionCurve]

end FreshGradientMinimax
