import SampleReuse.SlowPersistentLower
import SampleReuse.PersistentFiniteCap
import SampleReuse.PaddingAdmissible
import SampleReuse.RandomFrameEmbedding

open SecondOrder MeasureTheory
open scoped ENNReal
namespace SampleReuse
noncomputable section

def slowPaddedReply (M : Parameters) (ε : ℝ) {d : ℕ}
    (U : Point (FirstOrderDimension (slowBlockSize M ε) (slowLinks M ε)) →ₗᵢ[ℝ] Point d)
    (Θ : Fin (slowLinks M ε+1) → Fin (slowBlockSize M ε) → Bool)
    (x : Point d) (z : FirstOrderCoefficients (slowBlockSize M ε) (slowLinks M ε) (slowCoefficientRadius M ε)) :=
  richReply (fun z => paddedLoss U (slowSample M ε Θ z)) z x

theorem slowSample_smooth (M : Parameters) (ε : ℝ)
    (Θ : Fin (slowLinks M ε+1) → Fin (slowBlockSize M ε) → Bool)
    (z : FirstOrderCoefficients (slowBlockSize M ε) (slowLinks M ε) (slowCoefficientRadius M ε)) :
    ContDiff ℝ 2 (slowSample M ε Θ z) :=
  (scaledFirstOrderSample_contDiff Θ _ _ z).of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide)

/-- The calibrated stochastic expected lower bound holds in any ambient
dimension containing the constructed chain, with actual zero-padded losses. -/
theorem slow_padded_expected_lower {H S Ξ : Type} [MeasurableSpace Ξ]
    (M : Parameters) {ε : ℝ} (hc : SlowCalibratedConditions M ε) {d : ℕ}
    (U : Point (FirstOrderDimension (slowBlockSize M ε) (slowLinks M ε)) →ₗᵢ[ℝ] Point d)
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → PersistentStoppingAlgorithm (Point d) H (RichReply d) (Point d) S)
    (N : ℕ) (hN : (N:ℝ) ≤ slowQueryThreshold M ε)
    (hE : ∀ Θ (table : Fin (N+1) → FirstOrderCoefficients (slowBlockSize M ε)
      (slowLinks M ε) (slowCoefficientRadius M ε)), MeasurableSet {ξ |
        ‖gradient (paddedLoss U (slowPopulation M ε Θ))
          (finiteCapOutput (P ξ) (slowPaddedReply M ε U Θ) N table)‖ ≤ ε})
    (hs : ∀ Θ n, Measurable (fun w : Ξ × (ℕ → FirstOrderCoefficients (slowBlockSize M ε)
      (slowLinks M ε) (slowCoefficientRadius M ε)) => (P w.1).stopOnRun (slowPaddedReply M ε U Θ) w.2 n))
    (hsolve : ∀ Θ, (2/3:ℝ) ≤ (μ.prod (iidSampleTapeLaw (slowLaw M hc Θ))).real
      {w : Ξ × (ℕ → FirstOrderCoefficients (slowBlockSize M ε) (slowLinks M ε) (slowCoefficientRadius M ε)) |
        (P w.1).Halts (slowPaddedReply M ε U Θ) w.2 ∧
        ‖gradient (paddedLoss U (slowPopulation M ε Θ))
          ((P w.1).outputFor (slowPaddedReply M ε U Θ) w.2)‖ ≤ ε}) :
    ∃ Θ, Admissible (slowLaw M hc Θ).toMeasure M (paddedLoss U (slowPopulation M ε Θ))
        (fun z => paddedLoss U (slowSample M ε Θ z)) 0 ∧
      (N+1:ℕ) * ENNReal.ofReal (5/12) ≤
        ∫⁻ w : Ξ × (ℕ → FirstOrderCoefficients (slowBlockSize M ε) (slowLinks M ε) (slowCoefficientRadius M ε)),
          (P w.1).extendedCost (slowPaddedReply M ε U Θ) w.2 ∂μ.prod (iidSampleTapeLaw (slowLaw M hc Θ)) := by
  have hpop (Θ) : ContDiff ℝ 2 (slowPopulation M ε Θ) :=
    (calibrated_slow_sample_admissible M hc Θ).population_smooth
  have hstop (Θ) (ξ : Ξ) (tape) (n) :
      (projectStoppingAlgorithm U (P ξ)).stopOnRun (slowReply M ε Θ) tape n =
        (P ξ).stopOnRun (slowPaddedReply M ε U Θ) tape n :=
    projectStopping_stop U (P ξ) _ (slowSample_smooth M ε Θ) tape n
  have hhalt (Θ) (ξ : Ξ) (tape) :
      (projectStoppingAlgorithm U (P ξ)).Halts (slowReply M ε Θ) tape ↔
        (P ξ).Halts (slowPaddedReply M ε U Θ) tape :=
    projectStopping_halts U (P ξ) _ (slowSample_smooth M ε Θ) tape
  have hout (Θ) (ξ : Ξ) (tape) :
      (projectStoppingAlgorithm U (P ξ)).outputFor (slowReply M ε Θ) tape =
        isometryProjection U ((P ξ).outputFor (slowPaddedReply M ε U Θ) tape) :=
    projectStopping_output U (P ξ) _ (slowSample_smooth M ε Θ) tape
  have hcosteq (Θ) (ξ : Ξ) (tape) :
      (projectStoppingAlgorithm U (P ξ)).extendedCost (slowReply M ε Θ) tape =
        (P ξ).extendedCost (slowPaddedReply M ε U Θ) tape :=
    projectStopping_extendedCost U (P ξ) _ (slowSample_smooth M ε Θ) tape
  have hprojcap (Θ) (table : Fin (N+1) → FirstOrderCoefficients (slowBlockSize M ε)
      (slowLinks M ε) (slowCoefficientRadius M ε)) (ξ : Ξ) :
      persistentOriginalOutput (firstOrderStoppingCapPolicy (projectStoppingAlgorithm U (P ξ)) N)
        Θ (slowAmplitude (slowBlockSize M ε) ε) (slowDilation (slowBlockSize M ε)) table N =
      isometryProjection U (finiteCapOutput (P ξ) (slowPaddedReply M ε U Θ) N table) := by
    unfold firstOrderStoppingCapPolicy
    rw [persistentOutputPolicy_firstOrder]
    exact projectStopping_finiteCapOutput U (P ξ) (slowSample M ε Θ) (slowSample_smooth M ε Θ) N table
  have hE' := fun Θ table => hE Θ table
  have hEproj : ∀ Θ (table : Fin (N+1) → FirstOrderCoefficients (slowBlockSize M ε)
      (slowLinks M ε) (slowCoefficientRadius M ε)), MeasurableSet {ξ |
      ‖gradient (slowPopulation M ε Θ) (persistentOriginalOutput
        (firstOrderStoppingCapPolicy (projectStoppingAlgorithm U (P ξ)) N)
        Θ (slowAmplitude (slowBlockSize M ε) ε) (slowDilation (slowBlockSize M ε)) table N)‖ ≤ ε} := by
    intro Θ table
    simpa only [paddedLoss_gradient_norm U ((hpop Θ).differentiable (by norm_num)),hprojcap] using hE' Θ table
  have hsproj : ∀ Θ n, Measurable (fun w : Ξ × (ℕ → FirstOrderCoefficients (slowBlockSize M ε)
      (slowLinks M ε) (slowCoefficientRadius M ε)) =>
      (projectStoppingAlgorithm U (P w.1)).stopOnRun (slowReply M ε Θ) w.2 n) := by
    intro Θ n
    simpa only [hstop] using hs Θ n
  have hsolveproj : ∀ Θ, (2/3:ℝ) ≤ (μ.prod (iidSampleTapeLaw (slowLaw M hc Θ))).real
      {w : Ξ × (ℕ → FirstOrderCoefficients (slowBlockSize M ε) (slowLinks M ε) (slowCoefficientRadius M ε)) |
        (projectStoppingAlgorithm U (P w.1)).Halts (slowReply M ε Θ) w.2 ∧
        ‖gradient (slowPopulation M ε Θ)
          ((projectStoppingAlgorithm U (P w.1)).outputFor (slowReply M ε Θ) w.2)‖ ≤ ε} := by
    intro Θ
    simpa only [hhalt,hout,
      paddedLoss_gradient_norm U ((hpop Θ).differentiable (by norm_num))] using hsolve Θ
  obtain ⟨Θ,hΘ,hcost⟩ := slow_calibrated_expected_lower M hc μ
    (fun ξ => projectStoppingAlgorithm U (P ξ)) N hN hEproj hsproj hsolveproj
  refine ⟨Θ,?_,?_⟩
  · simpa only [map_zero] using hΘ.zero_pad (slowSample_smooth M ε Θ) U
  · simpa only [hcosteq] using hcost

end
end SampleReuse
