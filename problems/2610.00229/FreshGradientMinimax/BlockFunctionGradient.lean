import FreshGradientMinimax.EuclidBlockFamily

/-! Actual derivatives and dimension-independent gradient estimates for
sums of functions of disjoint Euclidean blocks. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace InnerProduct

theorem block_function_hasFDerivAt {k m : ℕ} {f : Euclid m → ℝ} {g : Euclid m → Euclid m}
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x) (x : Euclid (k * m)) :
    HasFDerivAt (fun y => ∑ i : Fin k, f (euclidBlock i y))
      (innerSL ℝ (euclidJoin (fun i => g (euclidBlock i x)))) x := by
  have h : HasFDerivAt (fun y => ∑ i : Fin k, f (euclidBlock i y))
      (∑ i : Fin k, (innerSL ℝ (g (euclidBlock i x))).comp (euclidBlock i)) x := by
    apply HasFDerivAt.sum
    intro i _
    exact (hf (euclidBlock i x)).comp x (euclidBlock i).hasFDerivAt
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, innerSL_apply,
    euclid_inner_family, euclidBlock_join]

theorem block_function_gradient_difference {k m : ℕ} {g : Euclid m → Euclid m} {L : ℝ}
    (hL : 0 ≤ L) (hg : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (x y : Euclid (k * m)) :
    ‖euclidJoin (fun i => g (euclidBlock i x)) - euclidJoin (fun i => g (euclidBlock i y))‖ ≤
      L * ‖x - y‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mp
  rw [euclidJoin_sub, euclidJoin_norm_sq, mul_pow, euclid_norm_sq_blocks, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := pow_le_pow_left₀ (norm_nonneg _) (hg (euclidBlock i x) (euclidBlock i y)) 2
  simpa only [mul_pow, map_sub] using h

end FreshGradientMinimax
