import UpperGhostFinite

/-! Finite ghost/actual expected-risk comparison from the constructed coupling,
its derived failure probability, and a bounded legal-output loss. -/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
namespace Task006.Full

theorem ghostProcess_risk_transfer {E B : Type*} [MeasurableSpace E] [MeasurableSpace B]
    [MeasurableEq E] (μ : Measure B) [IsProbabilityMeasure μ] (G : E → Set B)
    (hG : MeasurableSet {p : E × B | p.2 ∈ G p.1})
    (hpos : ∀ x, μ (G x) ≠ 0) (step : E × B → E) (hstep : Measurable step) (x0 : E)
    {q M : ℝ} (hq : 0 ≤ q) (hM : 0 ≤ M) (hbad : ∀ x, μ (G x)ᶜ ≤ ENNReal.ofReal q)
    (loss : E → ℝ) (hloss : Measurable loss) (hbound : ∀ x, 0 ≤ loss x ∧ loss x ≤ M) (n : ℕ) :
    (∫ j, loss j.1.1 ∂ghostProcessLaw μ G hG hpos step hstep x0 n) ≤
      (∫ j, loss j.1.2 ∂ghostProcessLaw μ G hG hpos step hstep x0 n) + M * (n * q) := by
  let π := ghostProcessLaw μ G hG hpos step hstep x0 n
  have hactual : Integrable (fun j : GhostState E => loss j.1.1) π := by
    apply Integrable.of_bound (hloss.comp (measurable_fst.comp measurable_fst)).aestronglyMeasurable M
    exact ae_of_all _ (fun j => by simp only [Function.comp_apply, Real.norm_eq_abs]; rw [abs_of_nonneg (hbound _).1]; exact (hbound _).2)
  have hghost : Integrable (fun j : GhostState E => loss j.1.2) π := by
    apply Integrable.of_bound (hloss.comp (measurable_snd.comp measurable_fst)).aestronglyMeasurable M
    exact ae_of_all _ (fun j => by simp only [Function.comp_apply, Real.norm_eq_abs]; rw [abs_of_nonneg (hbound _).1]; exact (hbound _).2)
  have heq : ∀ᵐ j ∂π, j ∈ ghostFailedᶜ → loss j.1.1 = loss j.1.2 := by
    filter_upwards [ghostProcess_agreement μ G hG hpos step hstep x0 n] with j hj
    intro hgood
    have hf : j.2 = false := Bool.eq_false_iff.mpr hgood
    exact congrArg loss (hj hf)
  have ht := coupled_expectation_transfer (G := ghostFailedᶜ) measurableSet_ghostFailed.compl
    hactual hghost (ae_of_all _ (fun j => (hbound j.1.2).1))
    (ae_of_all _ (fun j => (hbound j.1.1).2)) heq
  simp only [compl_compl] at ht
  have hp := ghostProcess_failure_real_le μ G hG hpos step hstep x0 hq hbad n
  exact ht.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hp hM))

#print axioms ghostProcess_risk_transfer
end Task006.Full
