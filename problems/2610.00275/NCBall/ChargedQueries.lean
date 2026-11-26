import NCBall.ProjectionTrace

/-! # Charging only queries that concern the hidden vector under study -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace NCBall

variable {S F : Type*} [MeasurableSpace S]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] {H : ℕ}

attribute [local irreducible] noisyHandleDirection

def reusableQueryCount (p : ReusableQueryPolicy S F H) :
    (t : ℕ) → LinearHistory S t → ℕ
  | 0, _ => 0
  | t + 1, h => by
      classical
      exact reusableQueryCount p t h.1 + if p.direction t h.1 = 0 then 0 else 1

omit [InnerProductSpace ℝ F] [BorelSpace F]
  [FiniteDimensional ℝ F] in
theorem reusableQueryCount_le (p : ReusableQueryPolicy S F H)
    (t : ℕ) (h : LinearHistory S t) : reusableQueryCount p t h ≤ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hp := ih h.1
    simp only [reusableQueryCount]
    split_ifs <;> omega

omit [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
theorem reusableQueryCount_measurable (p : ReusableQueryPolicy S F H) (t : ℕ) :
    Measurable (reusableQueryCount p t) := by
  classical
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    apply (ih.comp measurable_fst).add
    exact Measurable.ite (((p.measurable_direction t).comp measurable_fst)
      (measurableSet_singleton 0)) measurable_const measurable_const

/-- Queries with zero coefficient reveal nothing about this vector. Other
observations are charged, even when redundant, so this bound requires no rank test. -/
theorem reusable_posterior_charged_trace_loss {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ F)
    (p : ReusableQueryPolicy S F H) (σ : ℝ) (hσ : 0 < σ)
    (t : ℕ) (h : LinearHistory S t) :
    hiddenVarianceLoss b (linearPosteriorProjection (p.toLinear σ) t h) ≤
      reusableQueryCount p t h / σ ^ 2 := by
  induction t with
  | zero => simp [linearPosteriorProjection, hiddenVarianceLoss_zero, reusableQueryCount]
  | succ t ih =>
    change hiddenVarianceLoss b (residualUpdate (linearPosteriorProjection (p.toLinear σ) t h.1)
      ((p.toLinear σ).query t h.1)) ≤ _
    rw [hiddenVarianceLoss_update b (linearPosteriorProjection_isProjection _ _ _)]
    have hp := ih h.1
    by_cases hd : p.direction t h.1 = 0
    · have hz : (p.toLinear σ).query t h.1 = 0 := by
        change noisyHandleDirection F σ (p.handle t h.1) (p.direction t h.1) = 0
        rw [hd, map_zero]
      simpa [reusableQueryCount, hd, hz, normalizedInnovation] using hp
    · have hs := reusable_query_innovation_bound p σ hσ t h.1
      simp only [reusableQueryCount, if_neg hd, Nat.cast_add, Nat.cast_one, add_div]
      exact add_le_add hp hs

end NCBall
