import LowRank.CompressionScalar

/-! A fixed positive real power grows at most linearly in the relative
perturbation on 0 ≤ ε ≤ 1. The constant depends only on the exponent. -/

namespace LowRank
open Set

theorem exists_relative_rpow_growth {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → (1 + ε) ^ p - 1 ≤ C * ε := by
  let g : ℝ → ℝ := fun x => p * x ^ (p - 1)
  have hg : ContinuousOn g (Icc 1 2) := by
    intro x hx
    exact (continuousAt_const.mul (Real.continuousAt_rpow_const x (p - 1)
      (Or.inl (ne_of_gt (by linarith [hx.1]))))).continuousWithinAt
  obtain ⟨z, hz, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (1 : ℝ) 2).Nonempty from ⟨1, by constructor <;> norm_num⟩) hg
  refine ⟨g z, mul_pos hp (Real.rpow_pos_of_pos (by linarith [hz.1]) _), ?_⟩
  intro ε hε hε1
  rcases hε.eq_or_lt with hzero | hpos
  · subst ε
    simp
  have hxy : (1 : ℝ) < 1 + ε := by linarith
  have hcont : ContinuousOn (fun x : ℝ => x ^ p) (Icc 1 (1 + ε)) := by
    intro x hx
    exact (Real.hasDerivAt_rpow_const
      (Or.inl (ne_of_gt (by linarith [hx.1])))).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun x : ℝ => x ^ p) (Ioo 1 (1 + ε)) := by
    intro x hx
    exact (Real.hasDerivAt_rpow_const
      (Or.inl (ne_of_gt (by linarith [hx.1])))).differentiableAt.differentiableWithinAt
  obtain ⟨u, hu, hder⟩ := exists_deriv_eq_slope (fun x : ℝ => x ^ p) hxy hcont hdiff
  have hu12 : u ∈ Icc 1 2 := ⟨hu.1.le, by linarith [hu.2]⟩
  have hder' := (Real.hasDerivAt_rpow_const (p := p)
    (Or.inl (ne_of_gt (show 0 < u by linarith [hu.1])))).deriv
  rw [hder'] at hder
  have hs : ((1 + ε) ^ p - 1) / ε ≤ g z := by
    have := hmax hu12
    dsimp [g] at this
    simpa only [hder, Real.one_rpow, add_sub_cancel_left] using this
  exact (div_le_iff₀ hpos).mp hs

end LowRank
