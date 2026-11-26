import OracleParameterizedMeasurable

open MeasureTheory ProbabilityTheory

namespace Task006.Full
noncomputable section

namespace OracleAlgorithm

variable {d N : ℕ} {S Z : Type*} [MeasurableSpace S] [MeasurableSpace Z]

theorem informativeHandles_card_parameter_measurable (A : OracleAlgorithm d N S)
    (F : Z → Space d → ℝ → ℝ)
    (hF : Measurable (fun p : Z × (Space d × ℝ) => F p.1 p.2.1 p.2.2)) :
    Measurable (fun w : (Z × S) × (ℕ → ℝ) =>
      ((A.informativeHandles (F w.1.1) w.2 w.1.2).card : ℝ)) := by
  have hm : Measurable (fun w : (Z × S) × (ℕ → ℝ) =>
      A.weightedHandles (F w.1.1) w.1.2 nonzeroStatus w.2) := by
    unfold weightedHandles
    apply Measurable.ennreal_tsum
    intro h
    have hχ : Measurable (fun w : (Z × S) × (ℕ → ℝ) =>
        A.queriedIndicator (F w.1.1) w.1.2 h w.2) := by
      exact measurable_const.indicator (A.measurableSet_queriedBefore_parameter F hF h N)
    exact ((nonzeroStatus_measurable.comp ((measurable_pi_apply h).comp measurable_snd)).mul hχ).ennreal_ofReal
  have hr := hm.ennreal_toReal
  simpa only [A.weightedHandles_nonzero_eq,ENNReal.toReal_natCast] using hr

theorem informativeHandles_card_parameter_integrable (A : OracleAlgorithm d N S)
    (F : Z → Space d → ℝ → ℝ)
    (hF : Measurable (fun p : Z × (Space d × ℝ) => F p.1 p.2.1 p.2.2))
    (γ : Measure ((Z × S) × (ℕ → ℝ))) [IsFiniteMeasure γ] :
    Integrable (fun w : (Z × S) × (ℕ → ℝ) =>
      ((A.informativeHandles (F w.1.1) w.2 w.1.2).card : ℝ)) γ := by
  apply Integrable.of_bound (A.informativeHandles_card_parameter_measurable F hF).aestronglyMeasurable N
  apply Filter.Eventually.of_forall
  intro w
  rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast A.informativeHandles_card_le (F w.1.1) w.1.2 w.2

end OracleAlgorithm

namespace HardFamily

variable {d N : ℕ} {S : Type*} [MeasurableSpace S]

theorem informative_handle_prior_budget (alg : OracleAlgorithm d N S)
    (L A : ℝ) (hL : 0 < L) (hA : 16 ≤ A)
    (ν : Measure (Space d)) [IsProbabilityMeasure ν]
    (σ : Measure S) [IsProbabilityMeasure σ] :
    (∫ w : (Space d × S) × (ℕ → ℝ),
        ((alg.informativeHandles (fun x g => g * inner ℝ w.1.1 x) w.2 w.1.2).card : ℝ)
      ∂(ν.prod σ).prod (iidHandleLaw (law L A hA))) ≤ (4096 / A ^ 3) * N := by
  let F : Space d → Space d → ℝ → ℝ := fun θ x g => g * inner ℝ θ x
  have hF : Measurable (fun p : Space d × (Space d × ℝ) => F p.1 p.2.1 p.2.2) :=
    measurable_snd.snd.mul (measurable_fst.inner measurable_snd.fst)
  have hint := alg.informativeHandles_card_parameter_integrable F hF
    ((ν.prod σ).prod (iidHandleLaw (law L A hA)))
  rw [integral_prod _ hint]
  calc
    _ ≤ ∫ _z : Space d × S, ((4096 / A^3) * N) ∂ν.prod σ :=
      integral_mono hint.integral_prod_left (integrable_const _) (fun z =>
        informative_handle_budget alg L A hL hA z.1 z.2)
    _ = _ := by simp

end HardFamily
end
end Task006.Full
