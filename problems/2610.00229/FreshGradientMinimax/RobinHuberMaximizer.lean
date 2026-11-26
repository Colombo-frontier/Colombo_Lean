import FreshGradientMinimax.RobinHuber

/-! Existence and uniqueness of the actual flat-Huber dual maximizer, with
its quantitative displacement from the zero-threshold quadratic optimizer. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct

theorem robinHuber_max_exists (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (a b : ℝ) :
    ∃ y, ∀ z, robinHuberPotential n δ a b z ≤ robinHuberPotential n δ a b y :=
  strong_concave_maximum_exists (sq_pos_of_pos (robinStep_pos (show 0 < n + 2 by omega)))
    (robinHuber_strongConcave n hδ a b)
    (continuous_iff_continuousAt.mpr (fun y => (robinHuber_hasFDerivAt n hδ a b y).continuousAt))

def robinHuberMaximizer (n : ℕ) (δ a b : ℝ) (hδ : 0 ≤ δ) : Euclid (n + 2) :=
  Classical.choose (robinHuber_max_exists n hδ a b)

theorem robinHuberMaximizer_max (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (a b : ℝ) (y : Euclid (n + 2)) :
    robinHuberPotential n δ a b y ≤ robinHuberPotential n δ a b (robinHuberMaximizer n δ a b hδ) :=
  Classical.choose_spec (robinHuber_max_exists n hδ a b) y

theorem robinHuberMaximizer_gradient_zero (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (a b : ℝ) :
    robinHuberGradient n δ a b (robinHuberMaximizer n δ a b hδ) = 0 :=
  gradient_zero_at_global_max _ (robinHuber_hasFDerivAt n hδ a b _) (robinHuberMaximizer_max n hδ a b)

theorem robinHuberMaximizer_unique (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (a b : ℝ) (y : Euclid (n + 2))
    (hy : ∀ z, robinHuberPotential n δ a b z ≤ robinHuberPotential n δ a b y) :
    robinHuberMaximizer n δ a b hδ = y :=
  strong_concave_maximum_unique (sq_pos_of_pos (robinStep_pos (show 0 < n + 2 by omega)))
    (robinHuber_strongConcave n hδ a b) (robinHuber_hasFDerivAt n hδ a b)
    _ y (robinHuberMaximizer_max n hδ a b) hy

theorem robinHuberMaximizer_zero {n : ℕ} (hn : 10 ≤ n + 2) {a b : ℝ}
    (ha : |a| ≤ 3) (hb : |b| ≤ 3 / 2) :
    robinHuberMaximizer n 0 a b (le_refl 0) = robinQuadraticOptimizer n a b := by
  apply robinHuberMaximizer_unique
  intro y
  rw [robin_huber_zero_value hn ha hb]
  exact robin_huber_zero_max hn ha hb y

theorem robinHuber_gradient_perturbation (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (a b : ℝ) (y : Euclid (n + 2)) :
    ‖robinHuberGradient n δ a b y - robinHuberGradient n 0 a b y‖ ≤
      2 * δ * Real.sqrt (n + 3 : ℕ) := by
  have he : robinHuberGradient n δ a b y - robinHuberGradient n 0 a b y =
      -(affineBoundedGradient (robinIncidence (n + 2)) (robinEdgeShift n a b) δ 1000 y -
        affineBoundedGradient (robinIncidence (n + 2)) (robinEdgeShift n a b) 0 1000 y) := by
    unfold robinHuberGradient
    abel
  rw [he, norm_neg]
  apply (affineBoundedGradient_perturbation _ _ hδ (by norm_num) y).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (robinIncidence_opNorm (show 0 < n + 2 by omega)) hδ) (Real.sqrt_nonneg _)

theorem robinHuberMaximizer_displacement {n : ℕ} (hn : 10 ≤ n + 2) {δ a b : ℝ}
    (hδ : 0 ≤ δ) (ha : |a| ≤ 3) (hb : |b| ≤ 3 / 2) :
    ‖robinHuberMaximizer n δ a b hδ - robinQuadraticOptimizer n a b‖ ≤
      2 * (n + 2 : ℕ) ^ 2 * δ * Real.sqrt (n + 3 : ℕ) := by
  have h := strong_concave_gradient_monotone (robinHuber_strongConcave n hδ a b)
    (robinHuberMaximizer n δ a b hδ) (robinQuadraticOptimizer n a b)
  rw [robinHuberMaximizer_gradient_zero, sub_zero] at h
  have hc := residual_controls_distance (robinStep (n + 2) ^ 2)
    (robinHuberGradient n δ a b (robinQuadraticOptimizer n a b))
    (robinHuberMaximizer n δ a b hδ - robinQuadraticOptimizer n a b) h
  have hg := robinHuber_gradient_perturbation n hδ a b (robinQuadraticOptimizer n a b)
  rw [robin_huber_zero_gradient hn ha hb, sub_zero] at hg
  have hr := sq_pos_of_pos (robinStep_pos (show 0 < n + 2 by omega))
  calc
    _ ≤ (2 * δ * Real.sqrt (n + 3 : ℕ)) / robinStep (n + 2) ^ 2 :=
      (le_div_iff₀ hr).mpr (by simpa only [mul_comm] using hc.trans hg)
    _ = _ := by
      unfold robinStep
      field_simp
      ring

end FreshGradientMinimax
