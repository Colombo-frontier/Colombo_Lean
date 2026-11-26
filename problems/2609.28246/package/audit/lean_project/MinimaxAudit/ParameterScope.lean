import Mathlib

/-! Literal counterexamples to omitting sign conditions from the source's
intermediate parameter statements. They concern unrestricted local readings;
the actual positive hard-parameter choice is not contradicted. -/
namespace MinimaxAudit

/-- With the paper's n=2, tau=1 and c=-5, the asserted coordinate bound
is impossible for every vector, hence cannot hold for a fixed point. -/
theorem negative_seed_saddle_bound_impossible :
    ¬ ∃ r : Fin 4 → ℝ, ∀ j, |r j| ≤ (-5 : ℝ) + 2 * 2 * 1 := by
  rintro ⟨r, hr⟩
  have h := hr 0
  have h0 := abs_nonneg (r 0)
  norm_num at h
  linarith

/-- With lambda=-1, tau=R=1 and n=2 the uniform scalar approximation
right-hand side is negative, regardless of the two scalar values. -/
theorem negative_scale_uniform_bound_impossible (u v : ℝ) :
    ¬ |u-v| ≤ 3 * (-1 : ℝ) * 1 * 1 * Real.sqrt 2 := by
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have h0 := abs_nonneg (u-v)
  intro h
  nlinarith only [h,h0,hs]
end MinimaxAudit
