import SecondOrder.DyadicIntervals

/-!
The truncated increment inequality in `lem:charge` of source/main.tex.
The finite-law result below proves linear charging of drift and quadratic
charging of orthogonal random increments over the actual dyadic partition.
It is a foundation for, not a proof of, the adaptive stopped-process theorem.
-/

open scoped BigOperators InnerProductSpace
open SecondOrder

namespace SampleReuse

theorem min_sq_le_product {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) :
    min (s ^ 2) (r ^ 2) ≤ s * r := by
  rcases le_total s r with h | h
  · exact (min_le_left _ _).trans (by nlinarith)
  · exact (min_le_right _ _).trans (by nlinarith)

theorem min_split_linear {c u v : ℝ} (hc : 0 ≤ c) (hv : 0 ≤ v) :
    min c (2 * u + 2 * v) ≤ 2 * min c u + 2 * v := by
  by_cases h : c ≤ u
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans (by linarith)
  · rw [min_eq_right (le_of_not_ge h)]
    exact min_le_right _ _

variable {E : Type*} [NormedAddCommGroup E]

/-- Capping the squared displacement turns the drift contribution linear. -/
theorem truncated_increment {σ L : ℝ} (hσ : 0 ≤ σ) (hL : 0 ≤ L)
    (a z : E) :
    min (σ ^ 2) (L ^ 2 * ‖a + z‖ ^ 2) ≤
      2 * σ * L * ‖a‖ + 2 * L ^ 2 * ‖z‖ ^ 2 := by
  have hn : ‖a + z‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖z‖ ^ 2 := by
    have h := norm_add_le a z
    nlinarith [norm_nonneg (a + z), sq_nonneg (‖a‖ - ‖z‖)]
  have hs : min (σ ^ 2) (L ^ 2 * ‖a‖ ^ 2) ≤ σ * (L * ‖a‖) := by
    simpa only [mul_pow] using min_sq_le_product hσ (mul_nonneg hL (norm_nonneg a))
  calc
    _ ≤ min (σ ^ 2) (2 * (L ^ 2 * ‖a‖ ^ 2) + 2 * (L ^ 2 * ‖z‖ ^ 2)) :=
      min_le_min_left _ (by nlinarith [mul_le_mul_of_nonneg_left hn (sq_nonneg L)])
    _ ≤ 2 * min (σ ^ 2) (L ^ 2 * ‖a‖ ^ 2) + 2 * (L ^ 2 * ‖z‖ ^ 2) :=
      min_split_linear (sq_nonneg σ) (mul_nonneg (sq_nonneg L) (sq_nonneg ‖z‖))
    _ ≤ _ := by nlinarith

theorem truncated_sum_increment {ι : Type*} (s : Finset ι) (a z : ι → E)
    {σ L : ℝ} (hσ : 0 ≤ σ) (hL : 0 ≤ L) :
    min (σ ^ 2) (L ^ 2 * ‖∑ k ∈ s, (a k + z k)‖ ^ 2) ≤
      2 * σ * L * (∑ k ∈ s, ‖a k‖) + 2 * L ^ 2 * ‖∑ k ∈ s, z k‖ ^ 2 := by
  rw [Finset.sum_add_distrib]
  exact (truncated_increment hσ hL _ _).trans
    (add_le_add_right (mul_le_mul_of_nonneg_left (norm_sum_le _ _)
      (by positivity : 0 ≤ 2 * σ * L)) _)

section FiniteLaw

variable [InnerProductSpace ℝ E]

/-- The scalar cap remains inside expectation. Orthogonality eliminates cross
terms only for the martingale part, never for the adaptive drift. -/
theorem expected_truncated_interval {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]
    (p : PMF Ω) (s : Finset ι) (a z : ι → Ω → E)
    {σ L : ℝ} (hσ : 0 ≤ σ) (hL : 0 ≤ L)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → pmfMean p (fun w => ⟪z i w, z j w⟫_ℝ) = 0) :
    pmfMean p (fun w => min (σ ^ 2) (L ^ 2 * ‖∑ k ∈ s, (a k w + z k w)‖ ^ 2)) ≤
      2 * σ * L * (∑ k ∈ s, pmfMean p (fun w => ‖a k w‖)) +
      2 * L ^ 2 * (∑ k ∈ s, pmfMean p (fun w => ‖z k w‖ ^ 2)) := by
  have hb := pmfMean_mono p (fun w => truncated_sum_increment s
    (fun k => a k w) (fun k => z k w) hσ hL)
  simpa only [pmfMean_add, pmfMean_mul, pmfMean_finset_sum,
    pmfMean_norm_sum_sq p s z ho] using hb

/-- Summing over intervals of overlap at most `depth` charges each drift norm
and each martingale variance at most `depth` times. -/
theorem expected_truncated_overlap {Ω ι t : Type*} [Fintype Ω] [Fintype ι]
    [Fintype t] [DecidableEq t] (p : PMF Ω) (I : ι → Finset t) (depth : ℕ)
    (a z : t → Ω → E) {σ L : ℝ} (hσ : 0 ≤ σ) (hL : 0 ≤ L)
    (ho : ∀ i j, i ≠ j → pmfMean p (fun w => ⟪z i w, z j w⟫_ℝ) = 0)
    (hdepth : ∀ k, (Finset.univ.filter (fun i => k ∈ I i)).card ≤ depth) :
    pmfMean p (fun w => ∑ i,
      min (σ ^ 2) (L ^ 2 * ‖∑ k ∈ I i, (a k w + z k w)‖ ^ 2)) ≤
      2 * (depth : ℝ) * (σ * L * pmfMean p (fun w => ∑ k, ‖a k w‖) +
        L ^ 2 * pmfMean p (fun w => ∑ k, ‖z k w‖ ^ 2)) := by
  have hd := bounded_overlap_sum I depth hdepth
    (fun k => pmfMean p (fun w => ‖a k w‖))
    (fun k => pmfMean_nonneg p (fun _ => norm_nonneg _))
  have hz := bounded_overlap_sum I depth hdepth
    (fun k => pmfMean p (fun w => ‖z k w‖ ^ 2))
    (fun k => pmfMean_nonneg p (fun _ => sq_nonneg _))
  rw [pmfMean_finset_sum]
  have hb := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    expected_truncated_interval p (I i) a z hσ hL (fun j _ k _ hne => ho j k hne))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hb
  simp only [pmfMean_finset_sum, Finset.sum_add_distrib]
  nlinarith [mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 2 * σ * L),
    mul_le_mul_of_nonneg_left hz (by positivity : 0 ≤ 2 * L ^ 2)]

/-- Dyadic specialization with proved overlap, rather than an assumed tree
cost estimate. This is the finite-law, deterministic-checkpoint case. -/
theorem expected_truncated_dyadic {Ω : Type*} [Fintype Ω] (p : PMF Ω)
    (M depth : ℕ) (a z : Fin M → Ω → E) {σ L : ℝ} (hσ : 0 ≤ σ) (hL : 0 ≤ L)
    (ho : ∀ i j, i ≠ j → pmfMean p (fun w => ⟪z i w, z j w⟫_ℝ) = 0) :
    pmfMean p (fun w => ∑ i : Fin depth × Fin M,
      min (σ ^ 2) (L ^ 2 * ‖∑ k ∈ dyadicBlock M i.1.val i.2, (a k w + z k w)‖ ^ 2)) ≤
      2 * (depth : ℝ) * (σ * L * pmfMean p (fun w => ∑ k, ‖a k w‖) +
        L ^ 2 * pmfMean p (fun w => ∑ k, ‖z k w‖ ^ 2)) :=
  expected_truncated_overlap p (fun i : Fin depth × Fin M => dyadicBlock M i.1.val i.2)
    depth a z hσ hL ho dyadic_overlap

end FiniteLaw
end SampleReuse
