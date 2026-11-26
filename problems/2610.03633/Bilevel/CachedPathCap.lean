import Bilevel.InnerContraction
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Deterministic path-cap certificates from the chi-refinement upper proof.
These lemmas apply to actual gradient steps, including a hypothetical rejected
last step. Probability of the simultaneous accuracy event is a separate task.
-/
noncomputable section
open scoped BigOperators
namespace Bilevel.CachedPathCap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem norm_sq_le_two (u v : E) : ‖u‖^2 ≤ 2 * ‖v‖^2 + 2 * ‖u-v‖^2 := by
  have ht : ‖u‖ ≤ ‖v‖ + ‖u-v‖ := by
    have := norm_add_le v (u-v)
    rw [add_sub_cancel] at this
    exact this
  have hs := (sq_le_sq₀ (norm_nonneg u) (by positivity : 0 ≤ ‖v‖ + ‖u-v‖)).mpr ht
  nlinarith [sq_nonneg (‖v‖ - ‖u-v‖)]

/-- Descent controls the energy of computed vectors, not only true gradients. -/
theorem computed_energy_bound (F : E → ℝ) (g : E → E) (x G : ℕ → E)
    {Λ Δ lower e : ℝ} (hΛ : 0 < Λ)
    (hg : ∀ z, HasGradientAt F (g z) z)
    (hlip : ∀ z w, ‖g z - g w‖ ≤ Λ * ‖z-w‖)
    (hlower : ∀ z, lower ≤ F z) (hgap : F (x 0) - lower ≤ Δ)
    (n : ℕ) (hstep : ∀ i < n, x (i+1) = x i - Λ⁻¹ • G i)
    (he : ∀ i < n, ‖G i - g (x i)‖^2 ≤ e) :
    (∑ i ∈ Finset.range n, ‖G i‖^2) ≤ 4 * Λ * Δ + 4 * n * e := by
  have hd : ∀ i < n, F (x (i+1)) ≤ F (x i) -
      ‖g (x i)‖^2 / (2*Λ) + ‖G i - g (x i)‖^2 / (2*Λ) := by
    intro i hi
    rw [hstep i hi]
    exact Descent.inexact_descent F (x i) (g (x i)) (G i) Λ hΛ
      (InnerContraction.smooth_upper_model F g Λ hg hlip (x i))
  have hsum := Descent.sum_gradient_sq_bound (fun i => F (x i))
    (fun i => ‖g (x i)‖^2) (fun i => ‖G i - g (x i)‖^2) Λ Δ n hΛ
    (by linarith [hlower (x n)]) hd
  have herr : (∑ i ∈ Finset.range n, ‖G i - g (x i)‖^2) ≤ n * e := by
    calc
      _ ≤ ∑ _i ∈ Finset.range n, e := Finset.sum_le_sum (fun i hi => he i (Finset.mem_range.mp hi))
      _ = _ := by simp
  have hcomputed : (∑ i ∈ Finset.range n, ‖G i‖^2) ≤
      2 * (∑ i ∈ Finset.range n, ‖g (x i)‖^2) +
        2 * (∑ i ∈ Finset.range n, ‖G i - g (x i)‖^2) := by
    calc
      _ ≤ ∑ i ∈ Finset.range n, (2 * ‖g (x i)‖^2 + 2 * ‖G i - g (x i)‖^2) :=
        Finset.sum_le_sum (fun i _ => norm_sq_le_two (G i) (g (x i)))
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  linarith

/-- Every accurate prefix is strictly below the computable cap. -/
theorem good_prefix_below_cap (F : E → ℝ) (g : E → E) (x G : ℕ → E)
    {Λ Δ lower ε : ℝ} (hΛ : 0 < Λ) (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    (hg : ∀ z, HasGradientAt F (g z) z)
    (hlip : ∀ z w, ‖g z - g w‖ ≤ Λ * ‖z-w‖)
    (hlower : ∀ z, lower ≤ F z) (hgap : F (x 0) - lower ≤ Δ)
    (n N : ℕ) (hN : 0 < N) (hn : n ≤ N)
    (hstep : ∀ i < n, x (i+1) = x i - Λ⁻¹ • G i)
    (he : ∀ i < n, ‖G i - g (x i)‖ ≤ ε / 8) :
    (∑ i ∈ Finset.range n, ‖G i‖^2) < 16 * Λ * Δ + N * ε^2 := by
  have hs := computed_energy_bound F g x G hΛ hg hlip hlower hgap n hstep
    (fun i hi => (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (he i hi))
  have hn' : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hm := mul_le_mul_of_nonneg_right hn' (sq_nonneg ε)
  have hp : 0 < (N : ℝ) * ε^2 := by positivity
  have hD : 0 ≤ Λ * Δ := mul_nonneg hΛ.le hΔ
  nlinarith

/-- On a complete accurate path, the mean over the actual pre-update iterates
already meets epsilon/2. An independent uniform terminal index realizes this
finite average; the oracle need not be unbiased after caching. -/
theorem uniform_output_average (F : E → ℝ) (g : E → E) (x G : ℕ → E)
    {Λ Δ lower ε : ℝ} (hΛ : 0 < Λ) (hε : 0 ≤ ε)
    (hg : ∀ z, HasGradientAt F (g z) z)
    (hlip : ∀ z w, ‖g z-g w‖ ≤ Λ * ‖z-w‖)
    (hlower : ∀ z, lower ≤ F z) (hgap : F (x 0) - lower ≤ Δ)
    (n : ℕ) (hn : 0 < n) (horizon : 32*Λ*Δ ≤ n*ε^2)
    (hstep : ∀ i < n, x (i+1) = x i - Λ⁻¹ • G i)
    (he : ∀ i < n, ‖G i-g (x i)‖ ≤ ε/8) :
    (∑ i ∈ Finset.range n, ‖g (x i)‖) / n ≤ ε/2 := by
  have hd : ∀ i < n, F (x (i+1)) ≤ F (x i) -
      ‖g (x i)‖^2 / (2*Λ) + ‖G i - g (x i)‖^2 / (2*Λ) := by
    intro i hi
    rw [hstep i hi]
    exact Descent.inexact_descent F (x i) (g (x i)) (G i) Λ hΛ
      (InnerContraction.smooth_upper_model F g Λ hg hlip (x i))
  have hsum := Descent.sum_gradient_sq_bound (fun i => F (x i))
    (fun i => ‖g (x i)‖^2) (fun i => ‖G i-g (x i)‖^2) Λ Δ n hΛ
    (by linarith [hlower (x n)]) hd
  have herr : (∑ i ∈ Finset.range n, ‖G i-g (x i)‖^2) ≤ n*(ε/8)^2 := by
    calc
      _ ≤ ∑ _i ∈ Finset.range n, (ε/8)^2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (he i (Finset.mem_range.mp hi))
      _ = _ := by simp
  have hgSum : (∑ i ∈ Finset.range n, ‖g (x i)‖^2) ≤ n*ε^2/4 := by
    have hh : 0 ≤ (n : ℝ)*ε^2 := by positivity
    nlinarith
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n)
    (fun _ => (1 : ℝ)) (fun i => ‖g (x i)‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hcs
  have hm := hcs.trans (mul_le_mul_of_nonneg_left hgSum (by positivity : (0 : ℝ) ≤ n))
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_le_iff₀ hn').mpr
  have hnε : 0 ≤ ε / 2 * n := by positivity
  have hs0 : 0 ≤ ∑ i ∈ Finset.range n, ‖g (x i)‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  apply (sq_le_sq₀ hs0 hnε).mp
  nlinarith

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem path_distance_le_length (x : ℕ → E) (n : ℕ) :
    ‖x n - x 0‖ ≤ ∑ i ∈ Finset.range n, ‖x (i+1) - x i‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have ht := norm_sub_le_norm_sub_add_norm_sub (x (n+1)) (x n) (x 0)
    linarith

omit [CompleteSpace E] in
/-- This bound requires only accepted-step energy, even on failure histories. -/
theorem path_length_sq_bound (x G : ℕ → E) {Λ cap : ℝ} (hΛ : 0 < Λ)
    (n : ℕ) (hstep : ∀ i < n, x (i+1) = x i - Λ⁻¹ • G i)
    (hcap : (∑ i ∈ Finset.range n, ‖G i‖^2) ≤ cap) :
    (∑ i ∈ Finset.range n, ‖x (i+1) - x i‖)^2 ≤ n * cap / Λ^2 := by
  have heq : (∑ i ∈ Finset.range n, ‖x (i+1) - x i‖) =
      Λ⁻¹ * (∑ i ∈ Finset.range n, ‖G i‖) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hstep i (Finset.mem_range.mp hi)]
    simp [sub_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hΛ]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n)
    (fun _ => (1 : ℝ)) (fun i => ‖G i‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hcs
  have hc := hcs.trans (mul_le_mul_of_nonneg_left hcap (by positivity : (0 : ℝ) ≤ n))
  rw [heq, mul_pow]
  have hh := mul_le_mul_of_nonneg_left hc (sq_nonneg Λ⁻¹)
  convert hh using 1
  ring

omit [CompleteSpace E] in
theorem path_distance_bound (x G : ℕ → E) {Λ cap : ℝ} (hΛ : 0 < Λ)
    (n : ℕ) (hstep : ∀ i < n, x (i+1) = x i - Λ⁻¹ • G i)
    (hcap : (∑ i ∈ Finset.range n, ‖G i‖^2) ≤ cap) :
    ‖x n - x 0‖ ≤ Real.sqrt (n * cap) / Λ := by
  have hl := path_length_sq_bound x G hΛ n hstep hcap
  have hc0 : 0 ≤ cap := (Finset.sum_nonneg (fun i _ => sq_nonneg ‖G i‖)).trans hcap
  have hlen0 : 0 ≤ ∑ i ∈ Finset.range n, ‖x (i+1) - x i‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hr : (Real.sqrt (n * cap) / Λ)^2 = n * cap / Λ^2 := by
    rw [div_pow, Real.sq_sqrt (by positivity)]
  have hb : (∑ i ∈ Finset.range n, ‖x (i+1) - x i‖) ≤ Real.sqrt (n * cap) / Λ :=
    (sq_le_sq₀ hlen0 (by positivity)).mp (by rwa [hr])
  exact (path_distance_le_length x n).trans hb

end Bilevel.CachedPathCap
