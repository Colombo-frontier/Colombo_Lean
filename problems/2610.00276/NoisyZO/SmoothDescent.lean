import NoisyZO.VectorTaylor
import NoisyZO.GradientHolder

/-!
# First-order Taylor bounds from a Lipschitz gradient

The sharp order-one integral remainder gives the standard descent lemma in a
real Hilbert space.  Both its upper and lower forms are useful for assembling
strongly convex perturbations of a quadratic objective.
-/

open scoped ContDiff Gradient InnerProductSpace

namespace NoisyZO

noncomputable section

/-- Operator-norm increments of the first Fréchet derivative are exactly
gradient increments under the real Riesz isometry. -/
theorem norm_iteratedFDeriv_one_sub_eq_gradient_sub
    {d : ℕ} (f : Point d → ℝ) (x y : Point d) :
    ‖iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 f y‖ =
      ‖∇ f x - ∇ f y‖ := by
  calc
    ‖iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 f y‖ =
        ‖iteratedFDeriv ℝ 0 (∇ f) x -
          iteratedFDeriv ℝ 0 (∇ f) y‖ :=
      (norm_iteratedFDeriv_gradient_sub f x y).symm
    _ = ‖∇ f x - ∇ f y‖ := by
      let C := (continuousMultilinearCurryFin0 ℝ (Point d) (Point d)).symm
      change ‖C (∇ f x) - C (∇ f y)‖ = _
      rw [← C.map_sub, C.norm_map]

/-- Exact first-order expansion with the increment remainder used below. -/
theorem firstOrderTaylor_eq_add_holderRemainder
    {d : ℕ} (f : Point d → ℝ) (hsmooth : ContDiff ℝ 1 f)
    (x y : Point d) :
    f y = f x + ⟪∇ f x, y - x⟫_ℝ +
      holderTaylorRemainder f 1 x (y - x) := by
  have ht := vector_taylor_eq_sum_add_holderRemainder
    f 1 (by norm_num) x (y - x)
    (fun _t _ht ↦ hsmooth.contDiffAt)
  rw [show x + (y - x) = y by abel] at ht
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
    iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply,
    ← inner_gradient_left, add_assoc] using ht

/-- The two-sided first-order Taylor remainder bound (descent lemma). -/
theorem abs_firstOrderTaylor_remainder_le_of_gradient_lipschitz
    {d : ℕ} (f : Point d → ℝ) (hsmooth : ContDiff ℝ 1 f)
    (L : ℝ) (hL : 0 ≤ L)
    (hgrad : ∀ u v, ‖∇ f u - ∇ f v‖ ≤ L * ‖u - v‖)
    (x y : Point d) :
    |f y - f x - ⟪∇ f x, y - x⟫_ℝ| ≤
      L * ‖y - x‖ ^ 2 / 2 := by
  have hholder : ∀ u v,
      ‖iteratedFDeriv ℝ 1 f u - iteratedFDeriv ℝ 1 f v‖ ≤
        L * ‖u - v‖ := by
    intro u v
    rw [norm_iteratedFDeriv_one_sub_eq_gradient_sub]
    exact hgrad u v
  have hr := norm_holderTaylorRemainder_one_le
    f x (y - x) L hL hholder
  rw [Real.norm_eq_abs] at hr
  rw [firstOrderTaylor_eq_add_holderRemainder f hsmooth x y]
  ring_nf
  convert hr using 1 <;> ring

/-- Lower Taylor inequality implied by a Lipschitz gradient. -/
theorem firstOrderTaylor_lower_of_gradient_lipschitz
    {d : ℕ} (f : Point d → ℝ) (hsmooth : ContDiff ℝ 1 f)
    (L : ℝ) (hL : 0 ≤ L)
    (hgrad : ∀ u v, ‖∇ f u - ∇ f v‖ ≤ L * ‖u - v‖)
    (x y : Point d) :
    f x + ⟪∇ f x, y - x⟫_ℝ - L * ‖y - x‖ ^ 2 / 2 ≤ f y := by
  have h := abs_firstOrderTaylor_remainder_le_of_gradient_lipschitz
    f hsmooth L hL hgrad x y
  have hlo := neg_le_of_abs_le h
  linarith

end

end NoisyZO
