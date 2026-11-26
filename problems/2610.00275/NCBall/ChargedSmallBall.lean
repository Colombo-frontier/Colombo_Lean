import NCBall.ChargedQueries
import NCBall.ReusableSmallBall

/-! # Estimation before the room's own information budget is exhausted -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal
namespace NCBall

variable {S F : Type*} [MeasurableSpace S]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] {H : ℕ}

theorem charged_posterior_smallBall (p : ReusableQueryPolicy S F H)
    (σ : ℝ) (hσ : 0 < σ) (t : ℕ) (h : LinearHistory S t)
    (hn : 0 < Module.finrank ℝ F)
    (ht : (reusableQueryCount p t h : ℝ) < (Module.finrank ℝ F : ℝ) * σ ^ 2 / 16) (u : F) :
    (euclideanGaussianLaw (HandleLatent F H)).real
      {z | ‖(Real.sqrt (Module.finrank ℝ F : ℝ))⁻¹ • hiddenBlock F H
        (linearPosteriorMean (p.toLinear σ) t h + linearPosteriorProjection (p.toLinear σ) t h z)
        - u‖ ≤ 1 / 16} ≤ Real.exp (-(Module.finrank ℝ F : ℝ) / 8) := by
  let Q := linearPosteriorProjection (p.toLinear σ) t h
  let m := linearPosteriorMean (p.toLinear σ) t h
  let c := (Real.sqrt (Module.finrank ℝ F : ℝ))⁻¹
  have hQ : IsResidualProjection Q := linearPosteriorProjection_isProjection _ _ _
  have htrace : hiddenVarianceLoss (hiddenEigenbasis hQ) Q < (Module.finrank ℝ F : ℝ) / 16 := by
    have hb := reusable_posterior_charged_trace_loss (hiddenEigenbasis hQ) p σ hσ t h
    have hd : (reusableQueryCount p t h : ℝ) / σ ^ 2 < (Module.finrank ℝ F : ℝ) / 16 :=
      (div_lt_iff₀ (sq_pos_of_pos hσ)).mpr (by nlinarith)
    exact hb.trans_lt hd
  have he (z : HandleLatent F H) : c • hiddenBlock F H (m + Q z) - u =
      c • hiddenBlock F H (Q z) - (u - c • hiddenBlock F H m) := by
    rw [map_add, smul_add]
    abel
  change (euclideanGaussianLaw (HandleLatent F H)).real
    {z | ‖c • hiddenBlock F H (m + Q z) - u‖ ≤ 1 / 16} ≤ _
  simp_rw [he]
  exact residual_gaussian_smallBall Q hQ hn htrace _

/-- The total number of rounds is unrestricted. The bound concerns paths with
few charged queries, which is essential when other rooms generate many replies. -/
theorem charged_adaptive_estimation_bound (ν : Measure S) [IsProbabilityMeasure ν]
    (p : ReusableQueryPolicy S F H) (σ : ℝ) (hσ : 0 < σ) (t : ℕ)
    (hn : 0 < Module.finrank ℝ F)
    (u : LinearHistory S t → F) (hu : Measurable u) :
    (ν.prod (euclideanGaussianLaw (HandleLatent F H)))
      {w | (reusableQueryCount p t (linearTranscript (p.toLinear σ) t w) : ℝ) <
        (Module.finrank ℝ F : ℝ) * σ ^ 2 / 16 ∧
        ‖(Real.sqrt (Module.finrank ℝ F : ℝ))⁻¹ • hiddenBlock F H w.2 -
          u (linearTranscript (p.toLinear σ) t w)‖ ≤ 1 / 16} ≤
      ENNReal.ofReal (Real.exp (-(Module.finrank ℝ F : ℝ) / 8)) := by
  let B := {w : LinearHistory S t × HandleLatent F H |
    (reusableQueryCount p t w.1 : ℝ) < (Module.finrank ℝ F : ℝ) * σ ^ 2 / 16 ∧
    ‖(Real.sqrt (Module.finrank ℝ F : ℝ))⁻¹ • hiddenBlock F H w.2 - u w.1‖ ≤ 1 / 16}
  have hc := reusableQueryCount_measurable p t
  have hB : MeasurableSet B := by
    have hcm : Measurable (fun w : LinearHistory S t × HandleLatent F H =>
        (reusableQueryCount p t w.1 : ℝ)) := by fun_prop
    have hnm : Measurable (fun w : LinearHistory S t × HandleLatent F H =>
        ‖(Real.sqrt (Module.finrank ℝ F : ℝ))⁻¹ • hiddenBlock F H w.2 - u w.1‖) :=
      (((hiddenBlock F H).measurable.comp measurable_snd).const_smul _ |>.sub
        (hu.comp measurable_fst)).norm
    exact (measurableSet_lt hcm measurable_const).inter (measurableSet_le hnm measurable_const)
  apply adaptive_gaussian_event_bound ν (p.toLinear σ) t B hB
  intro h
  by_cases hb : (reusableQueryCount p t h : ℝ) < (Module.finrank ℝ F : ℝ) * σ ^ 2 / 16
  · have he := ENNReal.ofReal_le_ofReal (charged_posterior_smallBall p σ hσ t h hn hb (u h))
    rw [ofReal_measureReal] at he
    simpa only [B, Set.mem_setOf_eq, hb, true_and] using he
  · simp only [B, Set.mem_setOf_eq, hb, false_and, Set.setOf_false, measure_empty]
    exact zero_le _

end NCBall
