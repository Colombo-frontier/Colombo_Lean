import RandomizedFO2003.ScalarQuadraticStep

namespace RandomizedFO2003.Accelerated

open scoped BigOperators

variable {κ c θ : ℝ} (e p x : ℕ → ℝ)
    (hp0 : p 0 = x 0) (hp : ∀ n, p (n + 1) = x n)
    (hx : ∀ n, x (n + 1) = scalarAGDStep κ c θ (e n) (p n) (x n))

include hp0 hp hx

theorem scalar_nearly_convex_epoch_potential (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hlow : -θ ≤ κ) (hhigh : κ ≤ 1) (N : ℕ) :
    8 * θ * (scalarQuadratic κ c (x N) - scalarQuadratic κ c (x 0) +
      momentumWeight θ * (x N - p N) ^ 2) +
      3 * θ ^ 2 * ∑ k ∈ Finset.range N, (x (k + 1) - x k) ^ 2 ≤
        16 * ∑ k ∈ Finset.range N, (e k) ^ 2 := by
  induction N with
  | zero => simp [hp0]
  | succ n ih =>
    have hs := scalar_nearly_convex_step hθ hθ1 hlow hhigh c (e n) (p n) (x n)
    dsimp only at hs
    rw [← hx n] at hs
    rw [hp n, Finset.sum_range_succ, Finset.sum_range_succ]
    nlinarith

theorem scalar_nearly_convex_epoch (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hlow : -θ ≤ κ) (hhigh : κ ≤ 1) (N : ℕ) :
    8 * θ * (scalarQuadratic κ c (x N) - scalarQuadratic κ c (x 0)) +
      3 * θ ^ 2 * ∑ k ∈ Finset.range N, (x (k + 1) - x k) ^ 2 ≤
        16 * ∑ k ∈ Finset.range N, (e k) ^ 2 := by
  have hs := scalar_nearly_convex_epoch_potential e p x hp0 hp hx hθ hθ1 hlow hhigh N
  have hm : 0 ≤ 8 * θ * momentumWeight θ * (x N - p N) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hθ) (momentumWeight_nonneg hθ)) (sq_nonneg _)
  nlinarith

theorem scalar_concave_pairing_le (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hlow : -2 ≤ κ) (hneg : κ ≤ 0) (N : ℕ) :
    (x N - p N) * (κ * p N + c) ≤ errorBudget θ e N := by
  induction N with
  | zero => simp [hp0, errorBudget]
  | succ n ih =>
    rw [hp n, hx n, errorBudget]
    exact (scalar_concave_pairing_step hθ hθ1 hlow hneg c (e n) (p n) (x n)).trans
      (add_le_add_right (mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hθ1)) _)

theorem scalar_concave_epoch (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hlow : -2 ≤ κ) (hconcave : κ ≤ -θ) (N : ℕ) :
    2 * θ * (scalarQuadratic κ c (x N) - scalarQuadratic κ c (x 0)) +
      θ ^ 2 * ∑ k ∈ Finset.range N, (x (k + 1) - x k) ^ 2 ≤
        ∑ k ∈ Finset.range N, (e k) ^ 2 := by
  have hstep (n : ℕ) : scalarQuadratic κ c (x (n + 1)) - scalarQuadratic κ c (x n) ≤
      errorBudget θ e (n + 1) - θ / 2 * (x (n + 1) - x n) ^ 2 := by
    have hpair := scalar_concave_pairing_le e p x hp0 hp hx hθ hθ1 hlow (by linarith) (n + 1)
    rw [hp n] at hpair
    rw [scalarQuadratic_difference]
    have hc := mul_le_mul_of_nonneg_right hconcave (sq_nonneg (x (n + 1) - x n))
    nlinarith
  have hs := Finset.sum_le_sum (s := Finset.range N) (fun n _ => hstep n)
  rw [Finset.sum_range_sub (fun k => scalarQuadratic κ c (x k)) N,
    Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  have hscaled := mul_le_mul_of_nonneg_left hs hθ
  have hb := errorBudget_sum_le hθ1 e N
  nlinarith

/-- Uniform quadratic-model descent for every scalar spectral mode.
The two signs of curvature use different proved potentials, but the final
estimate has one set of constants and no sign-dependent hypothesis. -/
theorem scalar_quadratic_epoch (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hlow : -2 ≤ κ) (hhigh : κ ≤ 1) (N : ℕ) :
    8 * θ * (scalarQuadratic κ c (x N) - scalarQuadratic κ c (x 0)) +
      3 * θ ^ 2 * ∑ k ∈ Finset.range N, (x (k + 1) - x k) ^ 2 ≤
        16 * ∑ k ∈ Finset.range N, (e k) ^ 2 := by
  by_cases hc : -θ ≤ κ
  · exact scalar_nearly_convex_epoch e p x hp0 hp hx hθ hθ1 hc hhigh N
  · have hs := scalar_concave_epoch e p x hp0 hp hx hθ hθ1 hlow (le_of_lt (lt_of_not_ge hc)) N
    have hE : 0 ≤ ∑ k ∈ Finset.range N, (x (k + 1) - x k) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have he : 0 ≤ ∑ k ∈ Finset.range N, (e k) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    nlinarith [mul_nonneg (sq_nonneg θ) hE]

end RandomizedFO2003.Accelerated
