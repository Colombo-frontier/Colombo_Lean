import FreshGradientMinimax.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! A fully explicit coupled quadratic example: the primal gap and smoothness
remain fixed while the initial dual residual is arbitrary. This proves only
independence of the initialization parameters, NOT infinite oracle complexity.
This example has the known primal minimizer x = 1 and is not a hard family. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def translatedSaddle (M x y : ℝ) : ℝ := (x - 1) ^ 2 - (y - M - x) ^ 2 / 2
def translatedGradX (M x y : ℝ) : ℝ := x + y - M - 2
def translatedGradY (M x y : ℝ) : ℝ := M + x - y

theorem translated_derivative_x (M x y : ℝ) :
    HasDerivAt (fun t => translatedSaddle M t y) (translatedGradX M x y) x := by
  convert (((hasDerivAt_id x).sub_const 1).pow 2).sub
    ((((hasDerivAt_const x (y - M)).sub (hasDerivAt_id x)).pow 2).div_const 2) using 1
  simp [translatedSaddle, translatedGradX]
  ring

theorem translated_derivative_y (M x y : ℝ) :
    HasDerivAt (fun t => translatedSaddle M x t) (translatedGradY M x y) y := by
  convert (hasDerivAt_const y ((x - 1) ^ 2)).sub
    (((((hasDerivAt_id y).sub_const M).sub_const x).pow 2).div_const 2) using 1
  simp [translatedSaddle, translatedGradY]
  ring

/-- Exact joint Euclidean smoothness identity, uniform over the shift M. -/
theorem translated_gradient_difference (M x y x' y' : ℝ) :
    (translatedGradX M x y - translatedGradX M x' y') ^ 2 +
      (translatedGradY M x y - translatedGradY M x' y') ^ 2 =
      2 * ((x - x') ^ 2 + (y - y') ^ 2) := by
  unfold translatedGradX translatedGradY
  ring

/-- In particular the joint smoothness constant L = 2 works for every M. -/
theorem translated_joint_smooth (M x y x' y' : ℝ) :
    (translatedGradX M x y - translatedGradX M x' y') ^ 2 +
      (translatedGradY M x y - translatedGradY M x' y') ^ 2 ≤
      2 ^ 2 * ((x - x') ^ 2 + (y - y') ^ 2) := by
  rw [translated_gradient_difference]
  nlinarith [sq_nonneg (x - x'), sq_nonneg (y - y')]

/-- Exact strong-concavity remainder, with μ = 1. -/
theorem translated_strong_concavity (M x y y' : ℝ) :
    translatedSaddle M x y' = translatedSaddle M x y +
      translatedGradY M x y * (y' - y) - (y' - y) ^ 2 / 2 := by
  unfold translatedSaddle translatedGradY
  ring

theorem translated_value_le (M x y : ℝ) : translatedSaddle M x y ≤ (x - 1) ^ 2 := by
  unfold translatedSaddle
  nlinarith [sq_nonneg (y - M - x)]

theorem translated_value_attained (M x : ℝ) : translatedSaddle M x (M + x) = (x - 1) ^ 2 := by
  simp [translatedSaddle]

theorem translated_value_sup (M x : ℝ) :
    sSup (Set.range (translatedSaddle M x)) = (x - 1) ^ 2 := by
  apply IsGreatest.csSup_eq
  constructor
  · exact ⟨M + x, translated_value_attained M x⟩
  · rintro _ ⟨y, rfl⟩
    exact translated_value_le M x y

theorem translated_primal_inf : sInf (Set.range (fun x : ℝ => (x - 1) ^ 2)) = 0 := by
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨1, by norm_num⟩
  · rintro _ ⟨x, rfl⟩
    exact sq_nonneg _

theorem translated_initial_gap (M : ℝ) :
    sSup (Set.range (translatedSaddle M 0)) -
      sInf (Set.range (fun x => sSup (Set.range (translatedSaddle M x)))) = 1 := by
  simp_rw [translated_value_sup]
  rw [translated_primal_inf]
  norm_num

theorem translated_initial_residual (M : ℝ) : |translatedGradY M 0 0| = |M| := by
  simp [translatedGradY]

/-- Fixed gap 1, μ = 1 and joint smoothness L = 2 cannot bound the initial
dual residual. The example includes actual partial derivatives and maxima. -/
theorem gap_does_not_bound_dual_residual (G : ℝ) : ∃ M : ℝ,
    G < |translatedGradY M 0 0| ∧
    sSup (Set.range (translatedSaddle M 0)) -
      sInf (Set.range (fun x => sSup (Set.range (translatedSaddle M x)))) = 1 := by
  refine ⟨|G| + 1, ?_, translated_initial_gap _⟩
  rw [translated_initial_residual, abs_of_pos (by positivity : 0 < |G| + 1)]
  linarith [le_abs_self G]

end FreshGradientMinimax
