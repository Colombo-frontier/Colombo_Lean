import SampleReuse.RandomFrameAllDimensions
import SampleReuse.RandomFrameDimensionEnvelope

noncomputable section
namespace SampleReuse.RandomFrame
open MeasureTheory

/-- The deterministic curvature lower bound, in every sufficiently large
dimension, with a parameter-only dimension envelope and actual extended
expected evaluation cost. -/
theorem deterministic_curvature_uniform_lower (P : Parameters) :
    ∃ c C η : ℝ, 0 < c ∧ 0 < C ∧ 0 < η ∧ ∀ γ : ℝ, 0 < γ → γ < η →
      ∀ ε : ℝ, ε < P.gradientBound/8 → ∀ d : ℕ,
      ⌈C * (1 + Real.log (2/γ)/γ^4 + 1/γ^3)⌉₊ ≤ d →
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (π : StoppingFullJetPolicy d Ω),
      (∀ F, Admissible (PMF.pure ()).toMeasure P F (fun _ : Unit => F) 0 →
        (2/3:ℝ) ≤ μ.real {ω | π.Halts F ω ∧ IsSOSP F ε γ (π.outputFor F ω)}) →
      ∃ F, Admissible (PMF.pure ()).toMeasure P F (fun _ : Unit => F) 0 ∧
        ENNReal.ofReal (c/γ^3) ≤ ∫⁻ ω, π.extendedCost F ω ∂μ := by
  obtain ⟨c,ηL,hc,hηL,hlower⟩ := deterministic_curvature_expected_all_dimensions P
  obtain ⟨ηA,hηA,hamp⟩ := curvature_small_amplitude P
  refine ⟨c,frameDimensionConstant P,min ηL (min ηA 1),hc,
    frameDimensionConstant_pos P,lt_min hηL (lt_min hηA (by norm_num)),?_⟩
  intro γ hγ hγη ε hε d hd Ω _ μ _ π hsolve
  have hγL := hγη.trans_le (min_le_left ηL (min ηA 1))
  have hγA := (hγη.trans_le (min_le_right ηL (min ηA 1))).trans_le (min_le_left ηA 1)
  have hγ1 := (hγη.trans_le (min_le_right ηL (min ηA 1))).trans_le (min_le_right ηA 1)
  have hn := curvature_chain_length_bounds P hγ (hamp γ hγ hγA)
  have hN : curvatureChainLength P γ-1 < curvatureChainLength P γ := Nat.sub_lt hn.1 (by decide)
  have henv := calibrated_dimension_envelope P hγ hγ1.le hn.1 hN hn.2.2.2
  have hdim : calibratedFrameDimension P γ (curvatureChainLength P γ)
      (curvatureChainLength P γ-1) ≤ d := by
    apply Nat.cast_le (α := ℝ) |>.mp
    exact henv.trans ((Nat.le_ceil _).trans (by exact_mod_cast hd))
  exact hlower γ hγ hγL ε hε d hdim Ω μ π hsolve

end SampleReuse.RandomFrame
