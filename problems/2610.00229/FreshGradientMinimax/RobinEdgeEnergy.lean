import FreshGradientMinimax.RobinQuadratic

/-! The shifted squared incidence energy is the original chain edge energy.
Its expansion identifies the actual dual maximizer and value. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct

def robinEdgeShift (n : ℕ) (a b : ℝ) : Euclid (n + 3) :=
  -Real.sqrt (robinC (n + 2)) •
    (a • EuclideanSpace.single 0 1 + b • EuclideanSpace.single (Fin.last (n + 2)) 1)

def robinQuadraticEdges (n : ℕ) (a b : ℝ) (y : Euclid (n + 2)) : ℝ :=
  ‖robinIncidence (n + 2) y + robinEdgeShift n a b‖ ^ 2 / 2

def robinEdgeObjective (n : ℕ) (a b : ℝ) (y : Euclid (n + 2)) : ℝ :=
  robinSmallC (n + 2) * (a ^ 2 + b ^ 2) - robinStep (n + 2) ^ 2 / 2 * ‖y‖ ^ 2 -
    robinQuadraticEdges n a b y

theorem robinIncidence_first (n : ℕ) (y : Euclid (n + 2)) :
    robinIncidence (n + 2) y 0 = Real.sqrt (robinStep (n + 2)) * y 0 := by
  have hz : Fin.snoc (α := fun _ => ℝ) (fun j => y j) 0 (0 : Fin (n + 3)) = y 0 := by
    change Fin.snoc (α := fun _ => ℝ) (fun j => y j) 0 (0 : Fin (n + 2)).castSucc = _
    rw [Fin.snoc_castSucc]
  simp [robinIncidence, robinWeight, pathIncidence_apply, hz]

theorem robinIncidence_last (n : ℕ) (y : Euclid (n + 2)) :
    robinIncidence (n + 2) y (Fin.last (n + 2)) =
      -Real.sqrt (robinStep (n + 2)) * y (Fin.last (n + 1)) := by
  have hz : Fin.cons (α := fun _ => ℝ) 0 (fun j => y j) (Fin.last (n + 2)) = y (Fin.last (n + 1)) := by
    rw [← Fin.succ_last, Fin.cons_succ]
  simp only [robinIncidence, ContinuousLinearMap.comp_apply, coordinateMultiplier_apply,
    robinWeight, or_true, if_true, pathIncidence_apply, one_mul, Fin.snoc_last, hz]
  ring

theorem robinIncidence_interior {n : ℕ} (y : Euclid (n + 2)) (i : Fin (n + 1)) :
    robinIncidence (n + 2) y i.succ.castSucc = y i.succ - y i.castSucc := by
  have h0 : i.succ.castSucc ≠ (0 : Fin (n + 3)) := by
    intro h; have := congrArg Fin.val h; simp at this
  simp only [robinIncidence, ContinuousLinearMap.comp_apply, coordinateMultiplier_apply,
    robinWeight, h0, Fin.castSucc_ne_last, or_self, if_false, one_mul,
    pathIncidence_apply, Fin.snoc_castSucc]
  rw [← Fin.succ_castSucc, Fin.cons_succ]

theorem robinEdgeShift_norm_sq {n : ℕ} (hn : 10 ≤ n + 2) (a b : ℝ) :
    ‖robinEdgeShift n a b‖ ^ 2 = robinC (n + 2) * (a ^ 2 + b ^ 2) := by
  have h0 : (0 : Fin (n + 3)) ≠ Fin.last (n + 2) := by
    intro h; have := congrArg Fin.val h; simp at this
  have hC : 0 ≤ robinC (n + 2) := le_trans (by norm_num) (robin_coefficients_bounds hn).1
  simp [robinEdgeShift, norm_smul_sq, norm_add_sq_real, Real.sq_sqrt hC,
    real_inner_smul_left, real_inner_smul_right, EuclideanSpace.inner_single_left,
    EuclideanSpace.single_apply, h0, h0.symm]
  ring

theorem robin_source_scale {n : ℕ} (hn : 10 ≤ n + 2) :
    Real.sqrt (robinC (n + 2) / (n + 2 : ℕ)) =
      Real.sqrt (robinC (n + 2)) * Real.sqrt (robinStep (n + 2)) := by
  rw [div_eq_mul_inv, Real.sqrt_mul (le_trans (by norm_num) (robin_coefficients_bounds hn).1)]
  rfl

theorem robinEdgeShift_inner {n : ℕ} (hn : 10 ≤ n + 2) (a b : ℝ) (y : Euclid (n + 2)) :
    ⟪robinIncidence (n + 2) y, robinEdgeShift n a b⟫_ℝ =
      -⟪robinQuadraticSource n a b, y⟫_ℝ := by
  simp only [robinEdgeShift, robinQuadraticSource, robinEndpointSource, real_inner_smul_left,
    real_inner_smul_right, inner_add_right, inner_sub_left,
    EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right,
    EuclideanSpace.proj, map_one, mul_one, one_mul]
  rw [robinIncidence_first, robinIncidence_last, robin_source_scale hn]
  simp only [starRingEnd_apply, star_trivial]
  ring

theorem robinEdgeObjective_eq {n : ℕ} (hn : 10 ≤ n + 2) (a b : ℝ) (y : Euclid (n + 2)) :
    robinEdgeObjective n a b y = robinQuadraticObjective n a b y := by
  unfold robinEdgeObjective robinQuadraticEdges robinQuadraticObjective
  rw [norm_add_sq_real, robinEdgeShift_norm_sq hn, robinEdgeShift_inner hn]
  change _ = _ + _ - ⟪normalOperator (robinIncidence (n + 2)) (robinStep (n + 2) ^ 2) 1 y, y⟫_ℝ / 2
  rw [normalOperator_inner]
  ring

theorem robin_edge_elimination {n : ℕ} (hn : 10 ≤ n + 2) (a b : ℝ) :
    robinEdgeObjective n a b (robinQuadraticOptimizer n a b) = 6 * (a - b) ^ 2 ∧
      ∀ y, robinEdgeObjective n a b y ≤ 6 * (a - b) ^ 2 := by
  simp only [robinEdgeObjective_eq hn]
  exact ⟨robin_quadratic_elimination hn a b, robin_quadratic_max hn a b⟩

end FreshGradientMinimax
