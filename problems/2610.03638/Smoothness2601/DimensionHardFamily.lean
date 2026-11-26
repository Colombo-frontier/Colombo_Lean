import Smoothness2601.HardDimension

/-! The complete source lower-family dimension clause: the ambient dimension
is bounded and chosen before the algorithm; a valid scalar-inner hard
population and fresh oracle are chosen afterward. -/
noncomputable section
namespace Smoothness2601.HardProfiles
open MeasureTheory ProbabilityTheory
open Bilevel EuclideanGaussian ProjectionPosterior
open scoped ENNReal

theorem bounded_dimension_hard_family {b : Budgets} {M Λ β : ℝ}
    (W : WidthConstants b M Λ β) (hM : 0 < M) (hΛ : 0 < Λ)
    {p : WithTop ℕ} (hp : 1 ≤ p) (hβ : 0 ≤ β) {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ Real.exp (-1)) (hεs : 16*ε ≤ W.chainThreshold) (N : ℕ)
    (hN : (N : ℝ) ≤ W.finalRateConstant*ε^(-4 : ℝ)*(orderTradeoff p β ε)^2) :
    ∃ n : ℕ,
      (hardDimension N n : ℝ) ≤ dimensionCoefficient W*(ε⁻¹)^2*Real.log ε⁻¹ ∧
      ∀ A : Adaptive.Algorithm (Bilevel.EuclideanGaussian.Space (hardDimension N n)) ℝ,
        ∃ U : Frame (hardDimension N n) (n+1), ∃ hU : Orthonormal ℝ U,
          (population W hp hβ (by positivity : 0 < 16*ε)
            ((W.chainThreshold_conditions (by positivity) hεs).1)
            (FrameTruncation.frameIsometry U hU)).HigherRegularity p (derivativeEnvelope b M Λ β) ∧
          (population W hp hβ (by positivity : 0 < 16*ε)
            ((W.chainThreshold_conditions (by positivity) hεs).1)
            (FrameTruncation.frameIsometry U hU)).Initialized 0 0 ∧
          ENNReal.ofReal (2*ε) ≤ Adaptive.expectedNorm A
            (oracle W hp hβ (by positivity : 0 < 16*ε)
              ((W.chainThreshold_conditions (by positivity) hεs).1)
              (FrameTruncation.frameIsometry U hU)) N () 0 0 := by
  have hs : 0 < 16*ε := by positivity
  have hsδ := (W.chainThreshold_conditions hs hεs).1
  obtain ⟨n,hlo,hhi,hgap⟩ := W.choose_chain hs hεs
  have hbudget := W.budget_reveal hp hβ hs hεs hlo (W.scaled_budget hp hβ hε hεs hN)
  refine ⟨n,hardDimension_rate W hp hβ hε hsmall hN hhi,?_⟩
  intro A
  obtain ⟨U,hU,hfail⟩ := fixed_frame_expected_norm_chosen_dimension W hp hβ hs hsδ n N hbudget A
  refine ⟨U,hU,regularity W hp hβ hs hsδ (FrameTruncation.frameIsometry U hU) hM hΛ,
    initialized W hp hβ hs hsδ (FrameTruncation.frameIsometry U hU) hgap,?_⟩
  convert hfail using 1
  congr 1
  ring

end Smoothness2601.HardProfiles
