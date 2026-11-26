import RandomizedFO2003.OptimizationTaylor

namespace RandomizedFO2003.Accelerated

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The average includes index n, hence always has positive size. -/
noncomputable def prefixAverage (y : ℕ → E) (n : ℕ) : E :=
  ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ k ∈ Finset.range (n + 1), y k

theorem prefixAverage_const (x : E) (n : ℕ) : prefixAverage (fun _ => x) n = x := by
  simp only [prefixAverage, Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul]
  rw [inv_mul_cancel₀ (by positivity : ((n + 1 : ℕ) : ℝ) ≠ 0), one_smul]

theorem prefixAverage_sub (y z : ℕ → E) (n : ℕ) :
    prefixAverage (fun k => y k - z k) n = prefixAverage y n - prefixAverage z n := by
  simp only [prefixAverage, Finset.sum_sub_distrib, smul_sub]

theorem map_prefixAverage {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (y : ℕ → E) (n : ℕ) :
    A (prefixAverage y n) = prefixAverage (fun k => A (y k)) n := by
  simp only [prefixAverage, map_smul, map_sum]

theorem norm_prefixAverage_le (y : ℕ → E) (n : ℕ) {R : ℝ}
    (hy : ∀ k < n + 1, ‖y k‖ ≤ R) : ‖prefixAverage y n‖ ≤ R := by
  have hc : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hsum : ‖∑ k ∈ Finset.range (n + 1), y k‖ ≤ ((n + 1 : ℕ) : ℝ) * R := by
    calc
      _ ≤ ∑ k ∈ Finset.range (n + 1), ‖y k‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range (n + 1), R := Finset.sum_le_sum (fun k hk => hy k (Finset.mem_range.mp hk))
      _ = _ := by simp [nsmul_eq_mul]
  unfold prefixAverage
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hc.le)]
  calc
    _ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ * (((n + 1 : ℕ) : ℝ) * R) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hc.le)
    _ = R := by rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]

theorem norm_prefixAverage_sub_le (y : ℕ → E) (n : ℕ) (x : E) {R : ℝ}
    (hy : ∀ k < n + 1, ‖y k - x‖ ≤ R) : ‖prefixAverage y n - x‖ ≤ R := by
  have h := norm_prefixAverage_le (fun k => y k - x) n hy
  simpa only [prefixAverage_sub, prefixAverage_const] using h

end RandomizedFO2003.Accelerated

namespace RandomizedFO2003.Calculus

open RandomizedFO2003.Accelerated

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Averaging gradients is compatible with the affine quadratic model.
The discrepancy at the averaged point costs only ρ R². -/
theorem norm_gradient_prefixAverage_le {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    {ρ R : ℝ} (hρ : 0 ≤ ρ) (hR : 0 ≤ R)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖)
    (y : ℕ → E) (n : ℕ) (x : E) (hy : ∀ k < n + 1, ‖y k - x‖ ≤ R) :
    ‖gradient f (prefixAverage y n)‖ ≤
      ‖prefixAverage (fun k => gradient f (y k)) n‖ + ρ * R ^ 2 := by
  let H := fderiv ℝ (gradient f) x
  let e := fun k => gradient f (y k) - gradient f x - H (y k - x)
  have he : prefixAverage e n = prefixAverage (fun k => gradient f (y k)) n - gradient f x -
      H (prefixAverage y n - x) := by
    simp only [e, prefixAverage_sub, prefixAverage_const, ← map_prefixAverage, map_sub]
  have heR (k : ℕ) (hk : k < n + 1) : ‖e k‖ ≤ ρ / 2 * R ^ 2 := by
    apply (norm_gradient_linearization_error_le hf hH x (y k)).trans
    exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) hR).mpr (hy k hk)) (by positivity)
  have heAvg : ‖prefixAverage e n‖ ≤ ρ / 2 * R ^ 2 := norm_prefixAverage_le e n heR
  have hmean : ‖prefixAverage y n - x‖ ≤ R := norm_prefixAverage_sub_le y n x hy
  have hr : ‖gradient f (prefixAverage y n) - gradient f x - H (prefixAverage y n - x)‖ ≤
      ρ / 2 * R ^ 2 := (norm_gradient_linearization_error_le hf hH x _).trans
        (mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) hR).mpr hmean) (by positivity))
  have hid : gradient f (prefixAverage y n) =
      prefixAverage (fun k => gradient f (y k)) n +
        (gradient f (prefixAverage y n) - gradient f x - H (prefixAverage y n - x)) - prefixAverage e n := by
    rw [he]
    abel
  have hn := norm_sub_le
    (prefixAverage (fun k => gradient f (y k)) n +
      (gradient f (prefixAverage y n) - gradient f x - H (prefixAverage y n - x))) (prefixAverage e n)
  have ha := norm_add_le (prefixAverage (fun k => gradient f (y k)) n)
    (gradient f (prefixAverage y n) - gradient f x - H (prefixAverage y n - x))
  rw [← hid] at hn
  linarith

end RandomizedFO2003.Calculus
