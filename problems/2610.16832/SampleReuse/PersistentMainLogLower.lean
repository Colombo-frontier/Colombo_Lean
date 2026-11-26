import SampleReuse.PersistentMainLower

open SecondOrder MeasureTheory
open scoped ENNReal
namespace SampleReuse
noncomputable section

/-- The common stopping-policy minimax lower bound, with its explicit
inverse-cube sum and a single logarithmic denominator. -/
theorem persistent_main_log_lower (M : Parameters) :
    ∃ c C ε₀ γ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < ε₀ ∧ 0 < γ₀ ∧
      ∀ ε γ : ℝ, 0 < ε → ε ≤ ε₀ → 0 < γ → γ < γ₀ →
      ∀ d : ℕ, max (FirstOrderDimension (slowBlockSize M ε) (slowLinks M ε))
        ⌈C*(1+Real.log (2/γ)/γ^4+1/γ^3)⌉₊ ≤ d →
      ∀ (H S Ξ : Type) [MeasurableSpace S] [MeasurableSpace Ξ]
        (μ : Measure Ξ) [IsProbabilityMeasure μ]
        (P : Ξ → PersistentStoppingAlgorithm (Point d) H (RichReply d) (Point d) S),
      MeasurableStoppingFamily P → OperationallyMeasurable P →
      SolvesFiniteInstances (M := M) μ P ε γ →
      ∃ I : FiniteScalarInstance M d,
        ENNReal.ofReal (c*(1/ε^3+1/γ^3)/(1+Real.log (1/ε))) ≤
          finiteInstanceCost μ P I := by
  obtain ⟨c,C,ε₀,γ₀,hc,hC,hε₀,hγ₀,hmain⟩ := persistent_main_lower M
  refine ⟨c*(min (M.gap*slowModelScale M^2) 1/(2*slowLogConstant M)),C,
    min ε₀ 1,γ₀,mul_pos hc (sourceLowerEnvelope_log_coefficient_pos M),hC,
    lt_min hε₀ (by norm_num),hγ₀,?_⟩
  intro ε γ hε he hγ hg d hd H S Ξ _ _ μ _ P hmeas hop hsolve
  obtain ⟨I,hI⟩ := hmain ε γ hε (he.trans (min_le_left _ _)) hγ hg d hd
    H S Ξ μ P hmeas hop hsolve
  refine ⟨I,?_⟩
  have hrate := mul_le_mul_of_nonneg_left
    (sourceLowerEnvelope_log_rate M hε (he.trans (min_le_right _ _)) hγ) hc.le
  apply (ENNReal.ofReal_le_ofReal (show
    (c*(min (M.gap*slowModelScale M^2) 1/(2*slowLogConstant M)))*
      (1/ε^3+1/γ^3)/(1+Real.log (1/ε)) ≤ c*sourceLowerEnvelope M ε γ from ?_)).trans hI
  convert hrate using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end
end SampleReuse
