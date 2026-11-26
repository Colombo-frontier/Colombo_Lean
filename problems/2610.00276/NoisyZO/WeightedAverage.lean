import NoisyZO.Model
import NoisyZO.ProjectedSGDExpectation

/-!
# Jensen step for the SGD weighted output

The manuscript returns the average with weights proportional to
`1, 2, ..., n`.  Strong convexity implies ordinary convexity, so finite
Jensen converts the weighted sum of iterate gaps into the gap at the returned
point.  This discharges the deterministic `havg` premise of the final SGD
telescope theorem.
-/

open scoped BigOperators

namespace NoisyZO

noncomputable section

private lemma sum_range_succ_cast' (n : ℕ) :
    ∑ k ∈ Finset.range n, (k + 1 : ℝ) = (n : ℝ) * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- The normalized weighted average returned after `n` iterates. -/
def sgdWeightedAverage {d : ℕ} (n : ℕ) (x : ℕ → Point d) : Point d :=
  ∑ k ∈ Finset.range n,
    (2 * (k + 1 : ℝ) / ((n : ℝ) * (n + 1))) • x (k + 1)

private theorem sgd_weights_sum_one (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.range n,
      (2 * (k + 1 : ℝ) / ((n : ℝ) * (n + 1))) = 1 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1R : 0 < (n + 1 : ℝ) := by positivity
  calc
    ∑ k ∈ Finset.range n,
        (2 * (k + 1 : ℝ) / ((n : ℝ) * (n + 1))) =
        (2 / ((n : ℝ) * (n + 1))) *
          (∑ k ∈ Finset.range n, (k + 1 : ℝ)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
    _ = 1 := by
      rw [sum_range_succ_cast']
      field_simp [ne_of_gt hnR, ne_of_gt hn1R]

/-- Jensen's inequality in exactly the normalization used by the weighted SGD
telescope. -/
theorem NormalizedObjective.sgdWeightedAverage_gap_le
    {o : SmoothnessOrder} {d n : ℕ} (F : NormalizedObjective o d)
    (hn : 0 < n) (x : ℕ → Point d) :
    F.f (sgdWeightedAverage n x) - F.f F.minimizer ≤
      2 / ((n : ℝ) * (n + 1)) *
        (∑ k ∈ Finset.range n,
          (k + 1 : ℝ) * (F.f (x (k + 1)) - F.f F.minimizer)) := by
  let w : ℕ → ℝ := fun k ↦ 2 * (k + 1 : ℝ) / ((n : ℝ) * (n + 1))
  have hw0 : ∀ k ∈ Finset.range n, 0 ≤ w k := by
    intro k _
    dsimp [w]
    positivity
  have hw1 : ∑ k ∈ Finset.range n, w k = 1 := by
    simpa only [w] using sgd_weights_sum_one n hn
  have hjensen := F.convexOn_univ.map_sum_le hw0 hw1
    (fun _ _ ↦ Set.mem_univ _) (p := fun k ↦ x (k + 1))
  have hjensen' :
      F.f (sgdWeightedAverage n x) ≤
        ∑ k ∈ Finset.range n, w k * F.f (x (k + 1)) := by
    simpa only [sgdWeightedAverage, w, smul_eq_mul] using hjensen
  calc
    F.f (sgdWeightedAverage n x) - F.f F.minimizer ≤
        (∑ k ∈ Finset.range n, w k * F.f (x (k + 1))) -
          F.f F.minimizer := sub_le_sub_right hjensen' _
    _ = ∑ k ∈ Finset.range n,
        w k * (F.f (x (k + 1)) - F.f F.minimizer) := by
      calc
        (∑ k ∈ Finset.range n, w k * F.f (x (k + 1))) -
            F.f F.minimizer =
            (∑ k ∈ Finset.range n, w k * F.f (x (k + 1))) -
              (∑ k ∈ Finset.range n, w k) * F.f F.minimizer := by
                rw [hw1, one_mul]
        _ = ∑ k ∈ Finset.range n,
            w k * (F.f (x (k + 1)) - F.f F.minimizer) := by
              rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro k _
              ring
    _ = 2 / ((n : ℝ) * (n + 1)) *
        (∑ k ∈ Finset.range n,
          (k + 1 : ℝ) * (F.f (x (k + 1)) - F.f F.minimizer)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      dsimp [w]
      ring

/-- Complete deterministic assembly of the expected-step recurrence, weighted
telescope, and convex weighted-output comparison. -/
theorem NormalizedObjective.sgdWeightedAverage_final_bound
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (n : ℕ) (hn : 0 < n) (x : ℕ → Point d) (R : ℕ → ℝ)
    (B M : ℝ) (hM : 0 ≤ M) (hR : ∀ t, 0 ≤ R t)
    (hstep : ∀ k < n,
      R (k + 2) ≤
        (1 - (4 / (k + 2 : ℝ)) / 2) * R (k + 1) -
          2 * (4 / (k + 2 : ℝ)) *
            (F.f (x (k + 1)) - F.f F.minimizer) +
          2 * (4 / (k + 2 : ℝ)) * B ^ 2 +
          (4 / (k + 2 : ℝ)) ^ 2 * M) :
    F.f (sgdWeightedAverage n x) - F.f F.minimizer ≤
      B ^ 2 + 4 * M / (n + 1) := by
  apply biased_sgd_final_bound_of_expected_steps n hn R
    (fun t ↦ F.f (x t) - F.f F.minimizer) B M
    (F.f (sgdWeightedAverage n x) - F.f F.minimizer) hM hR hstep
  exact F.sgdWeightedAverage_gap_le hn x

end

end NoisyZO
