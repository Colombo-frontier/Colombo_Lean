import Mathlib

/-!
# Algebraic core of the minimax chain

This file verifies the finite-dimensional scalar identities used in
`source/main.tex`, equations `telescoping`, `energy2`, and `qpower`.
Indices below start at zero.  For the telescoping theorem the paper's length
is `n + 1`; `r 0` is its `r₁`.  The curvature sum is written in reverse
coordinate order, which does not change its scalar value.

No theorem here asserts that a derivative, oracle transcript, or randomized
hard instance has been constructed. Those analytic and information-theoretic
bridges remain separate audit obligations.
-/

namespace MinimaxAudit

/-- The ideal chain's scalar residual, with zero-based indexing. -/
def idealError (q c : ℝ) (r : ℕ → ℝ) : ℕ → ℝ
  | 0 => r 0 - c
  | k + 1 => r (k + 1) - q * r k

/-- Equation `telescoping`, for every nonempty chain. -/
theorem ideal_chain_telescoping (q c : ℝ) (r : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), q ^ (n - j) * idealError q c r j) =
      r n - q ^ n * c := by
  induction n with
  | zero => simp [idealError]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hscale :
        (∑ j ∈ Finset.range (n + 1),
          q ^ (n + 1 - j) * idealError q c r j) =
          q * ∑ j ∈ Finset.range (n + 1),
            q ^ (n - j) * idealError q c r j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjn : j ≤ n := by
        have : j < n + 1 := Finset.mem_range.mp hj
        omega
      have hexp : n + 1 - j = (n - j) + 1 := by omega
      rw [hexp, pow_succ]
      ring
    rw [hscale, ih]
    simp only [Nat.sub_self, pow_zero, one_mul, idealError, pow_succ]
    ring

/-- Scalar quadratic form of the symmetric tridiagonal Hessian, in
reverse coordinate order. There are `n + 1` diagonal terms. -/
def chainCurvatureEnergy (q : ℝ) (n : ℕ) : ℝ :=
  2 * (∑ i ∈ Finset.range (n + 1), (q ^ i) ^ 2) -
    2 * q * (∑ i ∈ Finset.range n, q ^ (i + 1) * q ^ i)

/-- Equation `energy2`: the energy equals two, for all real `q`,
without asymptotic estimates or positivity assumptions. -/
theorem chain_curvature_energy_eq_two (q : ℝ) (n : ℕ) :
    chainCurvatureEnergy q n = 2 := by
  induction n with
  | zero => simp [chainCurvatureEnergy]
  | succ n ih =>
    unfold chainCurvatureEnergy at ih ⊢
    have hs1 : (∑ i ∈ Finset.range (n + 1 + 1), (q ^ i) ^ 2) =
        (∑ i ∈ Finset.range (n + 1), (q ^ i) ^ 2) + (q ^ (n + 1)) ^ 2 :=
      Finset.sum_range_succ _ _
    have hs2 : (∑ i ∈ Finset.range (n + 1), q ^ (i + 1) * q ^ i) =
        (∑ i ∈ Finset.range n, q ^ (i + 1) * q ^ i) + q ^ (n + 1) * q ^ n :=
      Finset.sum_range_succ _ _
    rw [hs1, hs2]
    calc
      _ = 2 * (∑ i ∈ Finset.range (n + 1), (q ^ i) ^ 2) -
          2 * q * (∑ i ∈ Finset.range n, q ^ (i + 1) * q ^ i) := by
        rw [pow_succ]
        ring
      _ = 2 := ih

/-- The exact quadratic gain obtained after substituting the curvature
energy. This checks only the arithmetic after the manuscript's Taylor and
feasibility identities have been supplied. -/
theorem ideal_gap_gain_algebra (lam s : ℝ) (n : ℕ) (q : ℝ) :
    lam * (s ^ 2 - s ^ 2 / 4 * chainCurvatureEnergy q n) =
      lam / 2 * s ^ 2 := by
  rw [chain_curvature_energy_eq_two]
  ring


/-- A unit-decay geometric weight vector has squared Euclidean norm at
most its number of entries. -/
theorem geometric_weights_sq_sum_le (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), (q ^ (n - j)) ^ 2) ≤ (n + 1 : ℝ) := by
  calc
    _ ≤ ∑ j ∈ Finset.range (n + 1), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      have h0 : 0 ≤ q ^ (n - j) := pow_nonneg hq0 _
      have h1 : q ^ (n - j) ≤ 1 := pow_le_one₀ hq0 hq1
      nlinarith
    _ = (n + 1 : ℝ) := by simp

/-- Cauchy--Schwarz with the manuscript's geometric weight vector. -/
theorem weighted_error_abs_le (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (e : ℕ → ℝ) (n : ℕ) :
    |∑ j ∈ Finset.range (n + 1), q ^ (n - j) * e j| ≤
      Real.sqrt (n + 1) * Real.sqrt (∑ j ∈ Finset.range (n + 1), (e j) ^ 2) := by
  have hs0 : 0 ≤ ∑ j ∈ Finset.range (n + 1), (e j) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hn0 : (0 : ℝ) ≤ n + 1 := by positivity
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (n + 1))
    (fun j => q ^ (n - j)) e
  have hbound := mul_le_mul_of_nonneg_right
    (geometric_weights_sq_sum_le q hq0 hq1 n) hs0
  have habs := abs_nonneg (∑ j ∈ Finset.range (n + 1), q ^ (n - j) * e j)
  have hp0 := mul_nonneg (Real.sqrt_nonneg (n + 1))
    (Real.sqrt_nonneg (∑ j ∈ Finset.range (n + 1), (e j) ^ 2))
  have heq :
      (Real.sqrt (n + 1) * Real.sqrt (∑ j ∈ Finset.range (n + 1), (e j) ^ 2)) ^ 2 =
        (n + 1 : ℝ) * (∑ j ∈ Finset.range (n + 1), (e j) ^ 2) := by
    rw [mul_pow, Real.sq_sqrt hn0, Real.sq_sqrt hs0]
  nlinarith [sq_abs (∑ j ∈ Finset.range (n + 1), q ^ (n - j) * e j)]

/-- A uniformly bounded perturbation accumulates by at most length times
its bound when every geometric weight belongs to `[0,1]`. -/
theorem weighted_perturbation_abs_le (q tau : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (delta : ℕ → ℝ) (n : ℕ)
    (hdelta : ∀ j ∈ Finset.range (n + 1), |delta j| ≤ tau) :
    |∑ j ∈ Finset.range (n + 1), q ^ (n - j) * delta j| ≤ (n + 1 : ℝ) * tau := by
  calc
    _ ≤ ∑ j ∈ Finset.range (n + 1), |q ^ (n - j) * delta j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (n + 1), tau := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_of_nonneg (pow_nonneg hq0 _)]
      exact le_trans (mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ hq0 hq1))
        (hdelta j hj)
    _ = (n + 1 : ℝ) * tau := by simp

/-- Scalar gated residual coordinates. For the manuscript, take `delta 0 = 0`;
for later coordinates `delta j = T_(j+1) - q*r_j`. -/
def gatedError (q c : ℝ) (r delta : ℕ → ℝ) (j : ℕ) : ℝ :=
  idealError q c r j - delta j

/-- The exact perturbed telescoping identity used for gated residuals. -/
theorem gated_chain_telescoping (q c : ℝ) (r delta : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), q ^ (n - j) * gatedError q c r delta j) +
      (∑ j ∈ Finset.range (n + 1), q ^ (n - j) * delta j) =
        r n - q ^ n * c := by
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ j ∈ Finset.range (n + 1), q ^ (n - j) * idealError q c r j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [gatedError]
      ring
    _ = _ := ideal_chain_telescoping q c r n

/-- Lemma `gatedresidual` at the active-coordinate level, with a slightly
sharper explicit perturbation budget available through specialization.
The square-root sum is the Euclidean norm of the first `n+1` residual
coordinates. The passage to ambient `F` still needs the manuscript's
isometric-projection and derivative identities. -/
theorem gated_chain_residual_lower (q c rho tau : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (r delta : ℕ → ℝ) (n : ℕ)
    (hr : |r n| ≤ rho)
    (hdelta : ∀ j ∈ Finset.range (n + 1), |delta j| ≤ tau) :
    (q ^ n * c - rho - (n + 1 : ℝ) * tau) / Real.sqrt (n + 1) ≤
      Real.sqrt (∑ j ∈ Finset.range (n + 1), (gatedError q c r delta j) ^ 2) := by
  have htel := gated_chain_telescoping q c r delta n
  have he := weighted_error_abs_le q hq0 hq1 (gatedError q c r delta) n
  have hd := weighted_perturbation_abs_le q tau hq0 hq1 delta n hdelta
  have hr' : r n ≤ rho := le_trans (le_abs_self _) hr
  have hsum : q ^ n * c - rho ≤
      |∑ j ∈ Finset.range (n + 1), q ^ (n - j) * gatedError q c r delta j| +
      |∑ j ∈ Finset.range (n + 1), q ^ (n - j) * delta j| := by
    linarith [neg_le_abs (∑ j ∈ Finset.range (n + 1), q ^ (n - j) * gatedError q c r delta j),
      neg_le_abs (∑ j ∈ Finset.range (n + 1), q ^ (n - j) * delta j)]
  have hn : (0 : ℝ) < Real.sqrt (n + 1) := Real.sqrt_pos.2 (by positivity)
  apply (div_le_iff₀ hn).2
  nlinarith

/-- Lemma `idealresidual` at the active-coordinate level. -/
theorem ideal_chain_residual_lower (q c rho : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (r : ℕ → ℝ) (n : ℕ)
    (hr : |r n| ≤ rho) :
    (q ^ n * c - rho) / Real.sqrt (n + 1) ≤
      Real.sqrt (∑ j ∈ Finset.range (n + 1), (idealError q c r j) ^ 2) := by
  simpa [gatedError] using
    gated_chain_residual_lower q c rho 0 hq0 hq1 r (fun _ => 0) n hr (by simp)

end MinimaxAudit
