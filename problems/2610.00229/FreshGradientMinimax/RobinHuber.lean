import FreshGradientMinimax.RobinOptimizerEdges
import FreshGradientMinimax.AffineBoundedEnergy

/-! The uncapped bounded-slope Robin subchain. Its zero-threshold maximizer
and eliminated value are exactly those of the quadratic chain. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct

def robinHuberPotential (n : ℕ) (δ a b : ℝ) (y : Euclid (n + 2)) : ℝ :=
  robinSmallC (n + 2) * (a ^ 2 + b ^ 2) - robinStep (n + 2) ^ 2 / 2 * ‖y‖ ^ 2 -
    affineBoundedEnergy (robinIncidence (n + 2)) (robinEdgeShift n a b) δ 1000 y

def robinHuberGradient (n : ℕ) (δ a b : ℝ) (y : Euclid (n + 2)) : Euclid (n + 2) :=
  -(robinStep (n + 2) ^ 2 • y) -
    affineBoundedGradient (robinIncidence (n + 2)) (robinEdgeShift n a b) δ 1000 y

theorem robinHuber_hasFDerivAt (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (a b : ℝ) (y : Euclid (n + 2)) :
    HasFDerivAt (robinHuberPotential n δ a b) (innerSL ℝ (robinHuberGradient n δ a b y)) y := by
  have hnorm := (hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_mul (robinStep (n + 2) ^ 2 / 2)
  have hd := ((hasFDerivAt_const (robinSmallC (n + 2) * (a ^ 2 + b ^ 2)) y).sub hnorm).sub
    (affineBoundedEnergy_hasFDerivAt (robinIncidence (n + 2)) (robinEdgeShift n a b)
      (b := 1000) hδ (by norm_num) y)
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp [robinHuberGradient, innerSL_apply, inner_sub_left, inner_neg_left, real_inner_smul_left]
  ring

theorem robinHuber_strongConcave (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (a b : ℝ) :
    StrongConcaveGradient (robinHuberPotential n δ a b) (robinHuberGradient n δ a b) (robinStep (n + 2) ^ 2) := by
  simpa only [robinHuberPotential, robinHuberGradient, inner_zero_left, add_zero, zero_sub] using
    convex_penalty_strongConcave
      (affineBoundedEnergy_convex (robinIncidence (n + 2)) (robinEdgeShift n a b) hδ (by norm_num))
      (affineBoundedEnergy_hasFDerivAt (robinIncidence (n + 2)) (robinEdgeShift n a b) hδ (by norm_num))
      (robinStep (n + 2) ^ 2) (robinSmallC (n + 2) * (a ^ 2 + b ^ 2)) (0 : Euclid (n + 2))

theorem robinEdgeShift_adjoint {n : ℕ} (hn : 10 ≤ n + 2) (a b : ℝ) :
    ((robinIncidence (n + 2))†) (robinEdgeShift n a b) = -robinQuadraticSource n a b := by
  apply ext_inner_right ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left, inner_neg_left]
  calc
    _ = ⟪robinIncidence (n + 2) y, robinEdgeShift n a b⟫_ℝ := real_inner_comm _ _
    _ = _ := robinEdgeShift_inner hn a b y

theorem robin_huber_zero_gradient {n : ℕ} (hn : 10 ≤ n + 2) {a b : ℝ}
    (ha : |a| ≤ 3) (hb : |b| ≤ 3 / 2) :
    robinHuberGradient n 0 a b (robinQuadraticOptimizer n a b) = 0 := by
  have hcore : ∀ e, |(robinIncidence (n + 2) (robinQuadraticOptimizer n a b) + robinEdgeShift n a b) e| ≤ 1000 :=
    fun e => (robin_optimizer_all_edges hn ha hb e).trans (by norm_num)
  have hroot : robinStep (n + 2) ^ 2 • robinQuadraticOptimizer n a b +
      ((robinIncidence (n + 2))†) (robinIncidence (n + 2) (robinQuadraticOptimizer n a b)) =
      robinQuadraticSource n a b := by
    simpa only [robinOperator, normalOperator_apply, one_smul] using
      robinInverse_right (n := n + 2) (by omega) (robinQuadraticSource n a b)
  unfold robinHuberGradient affineBoundedGradient
  rw [boundedSlope_zero_core (by norm_num) _ hcore, map_add, robinEdgeShift_adjoint hn]
  rw [← hroot]
  abel

theorem robin_huber_zero_value {n : ℕ} (hn : 10 ≤ n + 2) {a b : ℝ}
    (ha : |a| ≤ 3) (hb : |b| ≤ 3 / 2) :
    robinHuberPotential n 0 a b (robinQuadraticOptimizer n a b) = 6 * (a - b) ^ 2 := by
  have hcore : ∀ e, |(robinIncidence (n + 2) (robinQuadraticOptimizer n a b) + robinEdgeShift n a b) e| ≤ 1000 :=
    fun e => (robin_optimizer_all_edges hn ha hb e).trans (by norm_num)
  unfold robinHuberPotential affineBoundedEnergy
  rw [boundedEnergy_zero_core (by norm_num) _ hcore]
  exact (robin_edge_elimination hn a b).1

theorem robin_huber_zero_max {n : ℕ} (hn : 10 ≤ n + 2) {a b : ℝ}
    (ha : |a| ≤ 3) (hb : |b| ≤ 3 / 2) (y : Euclid (n + 2)) :
    robinHuberPotential n 0 a b y ≤ 6 * (a - b) ^ 2 := by
  have h := robinHuber_strongConcave n (le_refl 0) a b (robinQuadraticOptimizer n a b) y
  rw [robin_huber_zero_gradient hn ha hb, inner_zero_left, add_zero,
    robin_huber_zero_value hn ha hb] at h
  exact h.trans (sub_le_self _ (by positivity))

end FreshGradientMinimax
