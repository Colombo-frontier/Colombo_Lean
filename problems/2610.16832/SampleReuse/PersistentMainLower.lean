import SampleReuse.SlowPaddedRate
import SampleReuse.PersistentCurvatureLower
import SampleReuse.ComplexityLogarithms

open SecondOrder MeasureTheory
open scoped ENNReal
namespace SampleReuse
noncomputable section

/-- Main expected total-query lower bound. One common arbitrary-handle
stopping policy is tested against actual admissible finite scalar-loss
instances in every dimension above the maximum of the two constructions. -/
theorem persistent_main_lower (M : Parameters) :
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
        ENNReal.ofReal (c*sourceLowerEnvelope M ε γ) ≤ finiteInstanceCost μ P I := by
  obtain ⟨cg,C,γ₀,hcg,hC,hγ₀,hcurv⟩ := persistent_curvature_uniform_lower M
  obtain ⟨η,hη,hsmall⟩ := slow_calibrated_conditions_small M
  refine ⟨min slowExpectedConstant cg,C,min η (M.gradientBound/16),γ₀,
    lt_min slowExpectedConstant_pos hcg,hC,
    lt_min hη (div_pos M.gradientBound_pos (by norm_num)),hγ₀,?_⟩
  intro ε γ hε hεsmall hγ hγsmall d hd H S Ξ _ _ μ _ P hmeas hop hsolve
  have hc := hsmall ε hε (hεsmall.trans (min_le_left _ _))
  have hεG : ε < M.gradientBound/8 := by
    have he := hεsmall.trans (min_le_right η (M.gradientBound/16))
    linarith [M.gradientBound_pos]
  let a := M.gap*(slowModelScale M)^2/(ε^3*slowAlpha (slowBlockSize M ε))
  let b := 1/γ^3
  have ha : 0 ≤ a := by have := M.gap_pos; have := slowAlpha_pos (slowBlockSize_pos M hε); dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  by_cases hab : b ≤ a
  · obtain ⟨I,hI⟩ := slow_padded_rate M hc ((le_max_left _ _).trans hd) μ P hop hsolve
    refine ⟨I,?_⟩
    have hs : min slowExpectedConstant cg*sourceLowerEnvelope M ε γ ≤
        slowExpectedConstant*M.gap*(slowModelScale M)^2/(ε^3*slowAlpha (slowBlockSize M ε)) := by
      change min slowExpectedConstant cg*max a b ≤ _
      rw [max_eq_left hab]
      have hh := mul_le_mul_of_nonneg_right (min_le_left slowExpectedConstant cg) ha
      dsimp [a] at hh
      convert hh using 1
      ring
    exact (ENNReal.ofReal_le_ofReal hs).trans hI
  · obtain ⟨f,hf,hcost⟩ := hcurv γ hγ hγsmall ε hεG d ((le_max_right _ _).trans hd)
      H S Ξ μ P hmeas (fun f hf => hsolve (pureScalarInstance f hf))
    refine ⟨pureScalarInstance f hf,?_⟩
    have hs : min slowExpectedConstant cg*sourceLowerEnvelope M ε γ ≤ cg/γ^3 := by
      change min slowExpectedConstant cg*max a b ≤ _
      rw [max_eq_right (le_of_not_ge hab)]
      have hh := mul_le_mul_of_nonneg_right (min_le_right slowExpectedConstant cg) hb
      dsimp [b] at hh
      convert hh using 1
      ring
    exact (ENNReal.ofReal_le_ofReal hs).trans hcost

end
end SampleReuse
