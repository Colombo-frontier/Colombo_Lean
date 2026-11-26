import FreshGradientMinimax.RobinEndpoint

/-! Exact elimination of one quadratic Robin subchain. All inverse entries
used in this computation have been proved for the actual finite operator. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct

theorem normal_quadratic_completion {n m : ℕ} (A : Euclid n →L[ℝ] Euclid m)
    {μ β : ℝ} (hμ : 0 < μ) (hβ : 0 ≤ β) (b y : Euclid n) :
    ⟪b, y⟫_ℝ - ⟪normalOperator A μ β y, y⟫_ℝ / 2 =
      ⟪b, normalInverse A μ β hμ hβ b⟫_ℝ / 2 -
        (μ * ‖y - normalInverse A μ β hμ hβ b‖ ^ 2 +
          β * ‖A (y - normalInverse A μ β hμ hβ b)‖ ^ 2) / 2 := by
  rw [← normalOperator_inner]
  simp only [map_sub, inner_sub_left, inner_sub_right, normalInverse_right]
  rw [normalOperator_symmetric A μ β y (normalInverse A μ β hμ hβ b),
    normalInverse_right, real_inner_comm y b]
  ring

def robinEndpointSource (n : ℕ) (a b : ℝ) : Euclid (n + 2) :=
  a • EuclideanSpace.single 0 1 - b • EuclideanSpace.single (Fin.last (n + 1)) 1

def robinQuadraticSource (n : ℕ) (a b : ℝ) : Euclid (n + 2) :=
  Real.sqrt (robinC (n + 2) / (n + 2 : ℕ)) • robinEndpointSource n a b

def robinQuadraticObjective (n : ℕ) (a b : ℝ) (y : Euclid (n + 2)) : ℝ :=
  (robinSmallC (n + 2) - robinC (n + 2) / 2) * (a ^ 2 + b ^ 2) +
    ⟪robinQuadraticSource n a b, y⟫_ℝ - ⟪robinOperator (n + 2) y, y⟫_ℝ / 2

def robinQuadraticOptimizer (n : ℕ) (a b : ℝ) : Euclid (n + 2) :=
  robinInverse (n + 2) (by omega) (robinQuadraticSource n a b)

theorem robinEndpointSource_inverse_inner {n : ℕ} (hn : 10 ≤ n + 2) (a b : ℝ) :
    ⟪robinEndpointSource n a b,
      robinInverse (n + 2) (by omega) (robinEndpointSource n a b)⟫_ℝ =
      (n + 2 : ℕ) * (robinA1 (n + 2) * (a ^ 2 + b ^ 2) - 2 * robinA2 (n + 2) * a * b) := by
  have hN : ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have h1 := (div_eq_iff hN).mp (robinInverse_entry_first hn)
  have h2 := (div_eq_iff hN).mp (robinInverse_entry_cross hn)
  have h3 := (div_eq_iff hN).mp (robinInverse_entry_last hn)
  have h4 := (div_eq_iff hN).mp (robinInverse_entry_cross_reverse hn)
  simp only [robinEndpointSource, map_sub, map_smul, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, EuclideanSpace.inner_single_left,
    EuclideanSpace.proj, map_one, one_mul]
  rw [h1, h2, h3, h4]
  ring

theorem robinQuadraticSource_inverse_inner {n : ℕ} (hn : 10 ≤ n + 2) (a b : ℝ) :
    ⟪robinQuadraticSource n a b, robinQuadraticOptimizer n a b⟫_ℝ =
      robinC (n + 2) * (robinA1 (n + 2) * (a ^ 2 + b ^ 2) - 2 * robinA2 (n + 2) * a * b) := by
  have hC : 0 ≤ robinC (n + 2) := le_trans (by norm_num) (robin_coefficients_bounds hn).1
  have hN : ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [robinQuadraticOptimizer, robinQuadraticSource, map_smul,
    real_inner_smul_left, real_inner_smul_right]
  rw [← mul_assoc, ← pow_two, Real.sq_sqrt (div_nonneg hC (Nat.cast_nonneg _)),
    robinEndpointSource_inverse_inner hn]
  field_simp
  ring

theorem robin_quadratic_elimination {n : ℕ} (hn : 10 ≤ n + 2) (a b : ℝ) :
    robinQuadraticObjective n a b (robinQuadraticOptimizer n a b) = 6 * (a - b) ^ 2 := by
  have hA2 : robinA2 (n + 2) ≠ 0 :=
    (lt_of_lt_of_le (by norm_num) (robin_endpoint_coefficient_bounds hn).1).ne'
  have hCA : robinC (n + 2) * robinA2 (n + 2) = 12 := by
    unfold robinC
    exact div_mul_cancel₀ _ hA2
  have hroot : robinOperator (n + 2) (robinQuadraticOptimizer n a b) =
      robinQuadraticSource n a b := robinInverse_right _ _
  unfold robinQuadraticObjective
  rw [hroot, robinQuadraticSource_inverse_inner hn]
  unfold robinSmallC
  linear_combination (a - b) ^ 2 / 2 * hCA

theorem robin_quadratic_gap {n : ℕ} (hn : 10 ≤ n + 2) (a b : ℝ) (y : Euclid (n + 2)) :
    6 * (a - b) ^ 2 - robinQuadraticObjective n a b y =
      (robinStep (n + 2) ^ 2 * ‖y - robinQuadraticOptimizer n a b‖ ^ 2 +
        ‖robinIncidence (n + 2) (y - robinQuadraticOptimizer n a b)‖ ^ 2) / 2 := by
  have h := normal_quadratic_completion (robinIncidence (n + 2))
    (sq_pos_of_pos (robinStep_pos (show 0 < n + 2 by omega))) (by norm_num : (0 : ℝ) ≤ 1)
    (robinQuadraticSource n a b) y
  have hm := robin_quadratic_elimination hn a b
  unfold robinQuadraticObjective at hm ⊢
  have hroot : robinOperator (n + 2) (robinQuadraticOptimizer n a b) =
      robinQuadraticSource n a b := robinInverse_right _ _
  rw [hroot] at hm
  change ⟪robinQuadraticSource n a b, y⟫_ℝ - ⟪robinOperator (n + 2) y, y⟫_ℝ / 2 =
    ⟪robinQuadraticSource n a b, robinQuadraticOptimizer n a b⟫_ℝ / 2 -
    (robinStep (n + 2) ^ 2 * ‖y - robinQuadraticOptimizer n a b‖ ^ 2 +
      1 * ‖robinIncidence (n + 2) (y - robinQuadraticOptimizer n a b)‖ ^ 2) / 2 at h
  linarith only [h, hm]

theorem robin_quadratic_max {n : ℕ} (hn : 10 ≤ n + 2) (a b : ℝ) (y : Euclid (n + 2)) :
    robinQuadraticObjective n a b y ≤ 6 * (a - b) ^ 2 := by
  have h := robin_quadratic_gap hn a b y
  have hnon : 0 ≤ (robinStep (n + 2) ^ 2 * ‖y - robinQuadraticOptimizer n a b‖ ^ 2 +
      ‖robinIncidence (n + 2) (y - robinQuadraticOptimizer n a b)‖ ^ 2) / 2 := by positivity
  linarith only [h, hnon]

end FreshGradientMinimax
