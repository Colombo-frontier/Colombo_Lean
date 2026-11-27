import Nonsmooth.QuadraticMarginalEnvelope

open MeasureTheory
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem quadratic_marginal_envelope_exists {E : Type} [NormedAddCommGroup E]
    (V : E → ℝ → ℝ) (hV : ∀ t, Continuous (V t)) {a B : ℝ} (ha : 0 < a) (hB : 0 < B)
    (hl : ∀ t x, a * (‖t‖ ^ 2 + x ^ 2) - B ≤ V t x)
    (hu : ∀ t x, V t x ≤ B * (1 + ‖t‖ ^ 2 + x ^ 2)) :
    ∃ K : ℝ, 0 < K ∧ ∀ t,
      a * ‖t‖ ^ 2 - K ≤ -Real.log (∫ x : ℝ, Real.exp (-V t x)) ∧
      -Real.log (∫ x : ℝ, Real.exp (-V t x)) ≤ K * (1 + ‖t‖ ^ 2) := by
  let A := Real.log (∫ x : ℝ, Real.exp (-a * x ^ 2))
  let D := Real.log (∫ x : ℝ, Real.exp (-B * x ^ 2))
  let K := B + |A| + |D| + 1
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro t
  have h := quadratic_marginal_potential_bounds V hV ha hB hl hu t
  change a * ‖t‖ ^ 2 - B - A ≤ _ ∧ _ ≤ B * (1 + ‖t‖ ^ 2) - D at h
  dsimp only [K]
  constructor
  · nlinarith [h.1, le_abs_self A, abs_nonneg D]
  · nlinarith [h.2, neg_abs_le D, abs_nonneg A,
      mul_nonneg (abs_nonneg A) (sq_nonneg ‖t‖),
      mul_nonneg (abs_nonneg D) (sq_nonneg ‖t‖), sq_nonneg ‖t‖]

end
end Nonsmooth
