import ParameterizedHandleCount

open MeasureTheory

set_option maxHeartbeats 1000000

namespace Task006.Full.HardFamily

noncomputable section
variable {d N : ℕ} {S Z : Type*} [MeasurableSpace S] [MeasurableSpace Z]

/-- The fresh-handle ledger is uniform over every independent exogenous
parameter law; a hidden direction and private seed can both be measurable
functions of that parameter. No prior information is returned to the policy. -/
theorem external_prior_handle_budget (alg : OracleAlgorithm d N S)
    (L A : ℝ) (hL : 0 < L) (hA : 16 ≤ A)
    (γ : Measure Z) [IsProbabilityMeasure γ]
    (θ : Z → Space d) (hθ : Measurable θ) (seed : Z → S) (hseed : Measurable seed) :
    Integrable (fun w : Z × (ℕ → ℝ) =>
      ((alg.informativeHandles (fun x g => g * inner ℝ (θ w.1) x) w.2 (seed w.1)).card : ℝ))
      (γ.prod (iidHandleLaw (law L A hA))) ∧
    (∫ w : Z × (ℕ → ℝ),
      ((alg.informativeHandles (fun x g => g * inner ℝ (θ w.1) x) w.2 (seed w.1)).card : ℝ)
      ∂γ.prod (iidHandleLaw (law L A hA))) ≤ (4096/A^3)*N := by
  let F : Z → Space d → ℝ → ℝ := fun z x g => g * inner ℝ (θ z) x
  have hF : Measurable (fun p : Z × (Space d × ℝ) => F p.1 p.2.1 p.2.2) :=
    measurable_snd.snd.mul ((hθ.comp measurable_fst).inner measurable_snd.fst)
  have hm : Measurable (fun w : Z × (ℕ → ℝ) =>
      ((alg.informativeHandles (F w.1) w.2 (seed w.1)).card : ℝ)) := by
    have hresult := (alg.informativeHandles_card_parameter_measurable F hF).comp
      ((measurable_fst.prodMk (hseed.comp measurable_fst)).prodMk measurable_snd)
    simpa only [Function.comp_def] using hresult
  have hint : Integrable (fun w : Z × (ℕ → ℝ) =>
      ((alg.informativeHandles (F w.1) w.2 (seed w.1)).card : ℝ))
      (γ.prod (iidHandleLaw (law L A hA))) := by
    apply Integrable.of_bound hm.aestronglyMeasurable N
    apply Filter.Eventually.of_forall
    intro w
    rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast alg.informativeHandles_card_le (F w.1) (seed w.1) w.2
  refine ⟨hint,?_⟩
  rw [integral_prod _ hint]
  calc
    _ ≤ ∫ _z : Z, ((4096/A^3)*N) ∂γ :=
      integral_mono hint.integral_prod_left (integrable_const _)
        (fun z => informative_handle_budget alg L A hL hA (θ z) (seed z))
    _ = _ := by simp

end
end Task006.Full.HardFamily
