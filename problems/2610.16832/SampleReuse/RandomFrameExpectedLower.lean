import SampleReuse.RandomFrameRate
import SampleReuse.RandomFrameExtendedCost

/-! Expected-query deterministic curvature hardness for genuine measurable
stopping policies. Expected cost is an extended nonnegative integral, including
infinity for nonhalting runs. All hard functions satisfy the manuscript model. -/

noncomputable section
namespace SampleReuse.RandomFrame

open MeasureTheory
open scoped ENNReal

theorem deterministic_curvature_expected_rate (P : Parameters) :
    ∃ c η : ℝ, 0 < c ∧ 0 < η ∧ ∀ γ : ℝ, 0 < γ → γ < η →
      ∀ ε : ℝ, ε < P.gradientBound/8 →
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (π : StoppingFullJetPolicy
          (calibratedFrameDimension P γ (curvatureChainLength P γ) (curvatureChainLength P γ-1)) Ω),
      (∀ F, Admissible (PMF.pure ()).toMeasure P F (fun _ : Unit => F) 0 →
        (2/3:ℝ) ≤ μ.real {ω | π.Halts F ω ∧ IsSOSP F ε γ (π.outputFor F ω)}) →
      ∃ F, Admissible (PMF.pure ()).toMeasure P F (fun _ : Unit => F) 0 ∧
        ENNReal.ofReal (c/γ^3) ≤ ∫⁻ ω, π.extendedCost F ω ∂μ := by
  obtain ⟨c₀,η,hc₀,hη,hrate⟩ := deterministic_curvature_rate P
  refine ⟨c₀/2,η,half_pos hc₀,hη,?_⟩
  intro γ hγ hγη ε hε Ω _ μ _ π hsolve
  obtain ⟨hnlower,hnupper,hfixed⟩ := hrate γ hγ hγη
  have hnpos : 0 < curvatureChainLength P γ := by
    exact_mod_cast (div_pos hc₀ (pow_pos hγ 3)).trans_le hnlower
  have hN : curvatureChainLength P γ-1 < curvatureChainLength P γ :=
    Nat.sub_lt hnpos (by decide)
  obtain ⟨F,hF,hcap⟩ := hfixed ε hε (curvatureChainLength P γ-1) hN Ω μ
    (π.cap (curvatureChainLength P γ-1))
  refine ⟨F,hF,?_⟩
  have hE := π.extended_expected_calls_from_cap hF.population_smooth μ (IsSOSP F ε γ)
    (curvatureChainLength P γ-1) (hsolve F hF) hcap
  have hN1 : curvatureChainLength P γ-1+1 = curvatureChainLength P γ :=
    Nat.sub_add_cancel hnpos
  rw [hN1] at hE
  have hr : (c₀/2)/γ^3 ≤ (curvatureChainLength P γ:ℝ)*((2/3:ℝ)-1/6) := by
    have he : (c₀/2)/γ^3 = (c₀/γ^3)/2 := by ring
    rw [he]
    nlinarith only [hnlower]
  have he : ENNReal.ofReal ((c₀/2)/γ^3) ≤
      (curvatureChainLength P γ:ℝ≥0∞)*ENNReal.ofReal ((2/3:ℝ)-1/6) := by
    calc
      _ ≤ ENNReal.ofReal ((curvatureChainLength P γ:ℝ)*((2/3:ℝ)-1/6)) :=
        ENNReal.ofReal_le_ofReal hr
      _ = _ := by rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  exact he.trans hE

end SampleReuse.RandomFrame
