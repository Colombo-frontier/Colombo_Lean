import FreshGradientMinimax.Basic

/-! Finite multilevel and epoch algebra used in F.1--F.4.
The stochastic construction of each level and its cost are separate analytic
obligations; no estimator with the desired moments is assumed to exist here. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
/-- Finite telescoping of level means; no infinite-series exchange is used. -/
theorem telescoping_level_means (H : ℕ → E) (K : ℕ) :
    H 0 + ∑ j ∈ Finset.range K, (H (j + 1) - H j) = H K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih]
    abel

/-- Mean of a finite importance-weighted correction is the final-level mean. -/
theorem multilevel_mean (H : ℕ → E) (p : ℕ → ℝ) (K : ℕ)
    (hp : ∀ j < K, p j ≠ 0) :
    H 0 + ∑ j ∈ Finset.range K, p j • ((p j)⁻¹ • (H (j + 1) - H j)) = H K := by
  have he : (∑ j ∈ Finset.range K, p j • ((p j)⁻¹ • (H (j + 1) - H j))) =
      ∑ j ∈ Finset.range K, (H (j + 1) - H j) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [smul_smul, hp j (Finset.mem_range.mp hj)]
  rw [he, telescoping_level_means]

theorem geometric_half_sum (K : ℕ) :
    (∑ j ∈ Finset.range K, (1 / 2 : ℝ) ^ (j + 1)) = 1 - (1 / 2 : ℝ) ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

def levelProbability (K j : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ (j + 1) / (1 - (1 / 2 : ℝ) ^ K)

theorem level_normalizer_pos {K : ℕ} (hK : 0 < K) : 0 < 1 - (1 / 2 : ℝ) ^ K := by
  have hp : (1 / 2 : ℝ) ^ K < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (Nat.ne_of_gt hK)
  linarith

theorem level_probabilities_sum {K : ℕ} (hK : 0 < K) :
    (∑ j ∈ Finset.range K, levelProbability K j) = 1 := by
  simp only [levelProbability, ← Finset.sum_div, geometric_half_sum]
  exact div_self (ne_of_gt (level_normalizer_pos hK))

theorem level_probability_pos {K : ℕ} (hK : 0 < K) (j : ℕ) :
    0 < levelProbability K j := by
  exact div_pos (by positivity) (level_normalizer_pos hK)

theorem multilevel_probability_mean {K : ℕ} (hK : 0 < K) (H : ℕ → E) :
    H 0 + ∑ j ∈ Finset.range K,
      levelProbability K j • ((levelProbability K j)⁻¹ • (H (j + 1) - H j)) = H K := by
  exact multilevel_mean H (levelProbability K) K (fun j _ => ne_of_gt (level_probability_pos hK j))

/-- Solving the stable affine recurrence used for the epoch energy in F.3. -/
theorem affine_recurrence_bound {p : ℕ → ℝ} {r b : ℝ} (hr : 0 ≤ r)
    (hrec : ∀ n, p (n + 1) ≤ r * p n + b) (n : ℕ) :
    p n ≤ r ^ n * p 0 + b * ∑ j ∈ Finset.range n, r ^ j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hi := mul_le_mul_of_nonneg_left ih hr
    have hs := hrec n
    have he : r * (∑ j ∈ Finset.range n, r ^ j) + 1 =
        ∑ j ∈ Finset.range (n + 1), r ^ j := by
      rw [Finset.sum_range_succ']
      simp only [← Finset.mul_sum, pow_succ', pow_zero]
    calc
      p (n + 1) ≤ r * (r ^ n * p 0 + b * ∑ j ∈ Finset.range n, r ^ j) + b := by linarith
      _ = r ^ (n + 1) * p 0 + b * (r * (∑ j ∈ Finset.range n, r ^ j) + 1) := by
        rw [pow_succ]
        ring
      _ = _ := by rw [he]

/-- Increasing inverse epoch envelopes incur a constant multiple of the last
inverse envelope, so this part of the stochastic cost has no epoch-count factor. -/
theorem geometric_epoch_cost {e : ℝ} (he : 0 < e) (K : ℕ) :
    (∑ j ∈ Finset.range K, (1 / 2 : ℝ) ^ (j + 1) / e) ≤ 1 / e := by
  rw [← Finset.sum_div, geometric_half_sum]
  apply div_le_div_of_nonneg_right _ he.le
  have : 0 ≤ (1 / 2 : ℝ) ^ K := by positivity
  linarith

/-- The exact telescoping identity for the gradient of recursive quadratic
regularizations in F.4. Weights may be arbitrary, not just powers of two. -/
theorem recursive_regularization_identity (w : ℕ → ℝ) (v : ℕ → E) (N : ℕ) :
    (∑ i ∈ Finset.range N, w i • (v N - v i)) =
      ∑ j ∈ Finset.range N, (∑ i ∈ Finset.range (j + 1), w i) • (v (j + 1) - v j) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hsplit : (∑ i ∈ Finset.range N, w i • (v (N + 1) - v i)) =
        (∑ i ∈ Finset.range N, w i • (v N - v i)) +
          (∑ i ∈ Finset.range N, w i) • (v (N + 1) - v N) := by
      rw [Finset.sum_smul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      module
    rw [hsplit, ih, Finset.sum_range_succ]
    module

end FreshGradientMinimax
