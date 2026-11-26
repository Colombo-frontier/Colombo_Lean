import NCBall.UpperRegret

/-! # Comparing a block of estimated gradients with its true gradients

The comparator may depend on the entire block. The difference between true
and estimated gradients is retained explicitly as one summed noise vector.
-/

noncomputable section
open scoped InnerProductSpace BigOperators
namespace NCBall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem exists_ball_dual_minimizer {D : ℝ} (hD : 0 ≤ D) (G : E) :
    ∃ u : E, ‖u‖ ≤ D ∧ ⟪G, u⟫_ℝ = -D * ‖G‖ := by
  by_cases hG : G = 0
  · subst G
    exact ⟨0, by simpa, by simp⟩
  have hn : 0 < ‖G‖ := norm_pos_iff.mpr hG
  refine ⟨-(D / ‖G‖) • G, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
    exact le_of_eq (div_mul_cancel₀ D (ne_of_gt hn))
  · rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
    ring

theorem clipped_block_gradient_norm {D α : ℝ} (hD : 0 ≤ D) (hα : 0 < α)
    (g a : ℕ → E) (s T : ℕ) :
    D * ‖∑ t ∈ Finset.range T, a (s + t)‖ ≤
      2 * D ^ 2 / α + (α / 2) * (∑ t ∈ Finset.range T, ‖g (s + t)‖ ^ 2) -
        (∑ t ∈ Finset.range T, ⟪g (s + t), clippedIncrement D hD α g (s + t)⟫_ℝ) +
        D * ‖∑ t ∈ Finset.range T, (g (s + t) - a (s + t))‖ := by
  obtain ⟨u, hu, hdual⟩ := exists_ball_dual_minimizer hD (∑ t ∈ Finset.range T, a (s + t))
  have hr := clipped_block_regret D hD hα g u hu s T
  have hsplit :
      (∑ t ∈ Finset.range T, ⟪g (s + t), clippedIncrement D hD α g (s + t) - u⟫_ℝ) =
        (∑ t ∈ Finset.range T, ⟪g (s + t), clippedIncrement D hD α g (s + t)⟫_ℝ) -
          ⟪∑ t ∈ Finset.range T, g (s + t), u⟫_ℝ := by
    simp only [inner_sub_right, Finset.sum_sub_distrib, sum_inner]
  have hsum : (∑ t ∈ Finset.range T, g (s + t)) =
      (∑ t ∈ Finset.range T, a (s + t)) +
        ∑ t ∈ Finset.range T, (g (s + t) - a (s + t)) := by
    rw [Finset.sum_sub_distrib]
    abel
  rw [hsplit, hsum, inner_add_left, hdual] at hr
  have hc := (real_inner_le_norm (∑ t ∈ Finset.range T, (g (s + t) - a (s + t))) u).trans
    (mul_le_mul_of_nonneg_left hu (norm_nonneg _))
  nlinarith

end NCBall
