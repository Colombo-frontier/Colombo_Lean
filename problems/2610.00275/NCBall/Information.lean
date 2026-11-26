import Mathlib.Tactic

/-!
# The spectral counting step of Lemma 8.2

This file proves the deterministic eigenvalue inequalities. It does NOT assert
that a transcript has a Gaussian conditional law or the stated covariance.
-/

noncomputable section
open scoped BigOperators
namespace NCBall

/-- Fewer than n/4 eigenvalues can exceed σ²/4 when the trace is below nσ²/16. -/
theorem few_large_eigenvalues {n : ℕ} (a : Fin n → ℝ) {σ2 : ℝ}
    (hσ : 0 < σ2) (ha : ∀ i, 0 ≤ a i)
    (htrace : ∑ i, a i < n * σ2 / 16) :
    ((Finset.univ.filter (fun i => σ2 / 4 < a i)).card : ℝ) < n / 4 := by
  classical
  let S := Finset.univ.filter (fun i => σ2 / 4 < a i)
  have hsum : (S.card : ℝ) * (σ2 / 4) ≤ ∑ i ∈ S, a i := by
    calc
      (S.card : ℝ) * (σ2 / 4) = ∑ _i ∈ S, σ2 / 4 := by simp
      _ ≤ ∑ i ∈ S, a i := Finset.sum_le_sum fun i hi =>
        le_of_lt (Finset.mem_filter.mp hi).2
  have hsub : ∑ i ∈ S, a i ≤ ∑ i, a i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => ha i)
  change (S.card : ℝ) < (n : ℝ) / 4
  nlinarith

/-- Each low precision eigenvalue gives the claimed posterior variance bound. -/
theorem posterior_variance_lower {n σ2 a : ℝ}
    (hn : 0 < n) (hσ : 0 < σ2) (ha : 0 ≤ a) (hsmall : a ≤ σ2 / 4) :
    4 / (5 * n) ≤ 1 / (n * (1 + a / σ2)) := by
  have hden : 0 < n * (1 + a / σ2) := by positivity
  apply (div_le_div_iff₀ (by positivity : 0 < 5 * n) hden).2
  have ha' : a / σ2 ≤ 1 / 4 := (div_le_iff₀ hσ).2 (by linarith)
  nlinarith

theorem many_small_eigenvalues {n : ℕ} (a : Fin n → ℝ) {σ2 : ℝ}
    (hσ : 0 < σ2) (ha : ∀ i, 0 ≤ a i)
    (htrace : ∑ i, a i < n * σ2 / 16) :
    3 * (n : ℝ) / 4 ≤ ((Finset.univ.filter (fun i => a i ≤ σ2 / 4)).card : ℝ) := by
  classical
  have hlarge := few_large_eigenvalues a hσ ha htrace
  have hc := Finset.filter_card_add_filter_neg_card_eq_card
    (s := Finset.univ (α := Fin n)) (fun i => σ2 / 4 < a i)
  simp only [not_lt, Finset.card_univ, Fintype.card_fin] at hc
  have hc' : ((Finset.univ.filter (fun i => σ2 / 4 < a i)).card : ℝ) +
      ((Finset.univ.filter (fun i => a i ≤ σ2 / 4)).card : ℝ) = n := by exact_mod_cast hc
  linarith

/-- A scalar query can enlarge the span of all observed directions by at most 1.
The rank theorem is deliberately separate from the Gaussian posterior theorem. -/
theorem query_budget {N : ℕ} (q : ℕ → ℕ) (hzero : q 0 = 0)
    (hstep : ∀ t < N, q (t + 1) ≤ q t + 1) : q N ≤ N := by
  have h : ∀ t ≤ N, q t ≤ t := by
    intro t
    induction t with
    | zero => simp [hzero]
    | succ t ih =>
      intro ht
      have hp := ih (by omega)
      have hs := hstep t (by omega)
      omega
  exact h N le_rfl

end NCBall
