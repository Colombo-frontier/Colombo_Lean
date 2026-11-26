import SampleReuse.SlowPaddedLower
import SampleReuse.SlowPersistentRate
import SampleReuse.PersistentLowerInterface

open SecondOrder MeasureTheory
open scoped ENNReal
namespace SampleReuse
noncomputable section

def slowPaddedInstance (M : Parameters) {ε : ℝ} (hc : SlowCalibratedConditions M ε) {d : ℕ}
    (U : Point (FirstOrderDimension (slowBlockSize M ε) (slowLinks M ε)) →ₗᵢ[ℝ] Point d)
    (Θ : Fin (slowLinks M ε+1) → Fin (slowBlockSize M ε) → Bool) : FiniteScalarInstance M d where
  Sample := FirstOrderCoefficients (slowBlockSize M ε) (slowLinks M ε) (slowCoefficientRadius M ε)
  finite := inferInstance
  measurable := inferInstance
  singletons := inferInstance
  law := slowLaw M hc Θ
  population := paddedLoss U (slowPopulation M ε Θ)
  sample := fun z => paddedLoss U (slowSample M ε Θ z)
  smooth z := (slowSample_smooth M ε Θ z).comp (isometryProjection U).contDiff
  admissible := by
    simpa only [map_zero] using (calibrated_slow_sample_admissible M hc Θ).zero_pad (slowSample_smooth M ε Θ) U

/-- The arbitrary-dimensional stochastic component in the common oracle
interface, with all hardness, law, count, and scalar premises discharged. -/
theorem slow_padded_rate {H S Ξ : Type} [MeasurableSpace Ξ]
    (M : Parameters) {ε γ : ℝ} (hc : SlowCalibratedConditions M ε) {d : ℕ}
    (hd : FirstOrderDimension (slowBlockSize M ε) (slowLinks M ε) ≤ d)
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → PersistentStoppingAlgorithm (Point d) H (RichReply d) (Point d) S)
    (hP : OperationallyMeasurable P) (hsolve : SolvesFiniteInstances (M := M) μ P ε γ) :
    ∃ I : FiniteScalarInstance M d,
      ENNReal.ofReal (slowExpectedConstant*M.gap*(slowModelScale M)^2/
        (ε^3*slowAlpha (slowBlockSize M ε))) ≤ finiteInstanceCost μ P I := by
  let U := RandomFrame.standardEmbedding hd
  let N := slowRateCap M ε
  have hF (Θ) : ∀ z, ContDiff ℝ 2 (paddedLoss U (slowSample M ε Θ z)) :=
    fun z => (slowSample_smooth M ε Θ z).comp (isometryProjection U).contDiff
  have hpop (Θ) : ContDiff ℝ 2 (paddedLoss U (slowPopulation M ε Θ)) :=
    (slowPaddedInstance M hc U Θ).admissible.population_smooth
  have hE (Θ) (table : Fin (N+1) → FirstOrderCoefficients (slowBlockSize M ε)
      (slowLinks M ε) (slowCoefficientRadius M ε)) : MeasurableSet {ξ |
        ‖gradient (paddedLoss U (slowPopulation M ε Θ))
          (finiteCapOutput (P ξ) (slowPaddedReply M ε U Θ) N table)‖ ≤ ε} := by
    apply measurableSet_le _ measurable_const
    exact ((contDiff_gradient_one (hpop Θ)).continuous.norm.measurable).comp
      (hP.finite_output _ _ (hF Θ) N table)
  have hs (Θ) (n) : Measurable (fun w : Ξ × (ℕ → FirstOrderCoefficients (slowBlockSize M ε)
      (slowLinks M ε) (slowCoefficientRadius M ε)) =>
      (P w.1).stopOnRun (slowPaddedReply M ε U Θ) w.2 n) :=
    hP.stop_run _ _ (hF Θ) n
  have hsol (Θ) : (2/3:ℝ) ≤ (μ.prod (iidSampleTapeLaw (slowLaw M hc Θ))).real
      {w : Ξ × (ℕ → FirstOrderCoefficients (slowBlockSize M ε) (slowLinks M ε) (slowCoefficientRadius M ε)) |
        (P w.1).Halts (slowPaddedReply M ε U Θ) w.2 ∧
        ‖gradient (paddedLoss U (slowPopulation M ε Θ))
          ((P w.1).outputFor (slowPaddedReply M ε U Θ) w.2)‖ ≤ ε} := by
    apply (hsolve (slowPaddedInstance M hc U Θ)).trans
    apply measureReal_mono
    · intro w hw
      exact ⟨hw.1,hw.2.1⟩
    · exact measure_ne_top (μ.prod (iidSampleTapeLaw (slowLaw M hc Θ))) _
  obtain ⟨Θ,_hI,hcost⟩ := slow_padded_expected_lower M hc U μ P N
    (slowRateCap_le M hc.tolerance_pos) hE hs hsol
  refine ⟨slowPaddedInstance M hc U Θ,?_⟩
  have hr := slowRateCap_rate M ε
  rw [← slowAlpha_rpow] at hr
  exact hr.trans hcost

end
end SampleReuse
