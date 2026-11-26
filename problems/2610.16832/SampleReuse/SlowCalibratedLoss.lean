import SampleReuse.SlowCalibration
import SecondOrder.FirstOrderEndpointAsymptotics

open SecondOrder MeasureTheory Filter
open scoped Topology

namespace SampleReuse
noncomputable section

def slowBlockSize (P : Parameters) (ε : ℝ) : ℕ :=
  firstOrderEndpointBlockSize P.gap (slowModelScale P) ε

def slowLinks (P : Parameters) (ε : ℝ) : ℕ :=
  firstOrderBudgetLinks P.gap (slowAmplitude (slowBlockSize P ε) ε)

theorem slowBlockSize_pos (P : Parameters) {ε : ℝ} (hε : 0 < ε) : 0 < slowBlockSize P ε :=
  (firstOrderEndpointBlockSize_bounds P.gap_pos.le hε).1

theorem slowAlpha_le_dimension {d : ℕ} (hd : 0 < d) : slowAlpha d ≤ d := by
  have ha := slowAlpha_ge_one hd
  have hf := slowAlpha_fourth d
  have hpow := pow_le_pow_right₀ ha (show 1 ≤ 4 by decide)
  simpa only [pow_one,hf] using hpow

theorem slow_amplitude_tendsto (P : Parameters) :
    Tendsto (fun ε : ℝ => slowAmplitude (slowBlockSize P ε) ε) (𝓝[>] 0) (𝓝 0) := by
  have hh : Tendsto (fun ε : ℝ => (slowBlockSize P ε:ℝ)*ε) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_one] using firstOrderEndpointBlockSize_mul_rpow_tendsto
      (s := slowModelScale P) P.gap_pos.le (by norm_num : (0:ℝ)<1)
  have hu := hh.const_mul (4/firstOrderGradientConstant)
  simp only [mul_zero] at hu
  apply squeeze_zero' _ _ hu
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (slowAmplitude_pos (slowBlockSize_pos P hε) hε).le
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    have hl := slowAlpha_le_dimension (slowBlockSize_pos P hε)
    have hm := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 4*ε)
    have hm' := div_le_div_of_nonneg_right hm firstOrderGradientConstant_pos.le
    unfold slowAmplitude
    convert hm' using 1
    ring

structure SlowCalibratedConditions (P : Parameters) (ε : ℝ) : Prop where
  tolerance_pos : 0 < ε
  coefficient_small : ε ≤ slowBiasConstant*slowModelScale P/256
  amplitude_small : 160*slowAmplitude (slowBlockSize P ε) ε ≤ P.gap
  population_small :
    slowPopulationGradientConstant*Real.sqrt (P.gap/(10*firstOrderGradientConstant))*Real.sqrt ε ≤
      P.gradientBound

theorem slow_calibrated_conditions_small (P : Parameters) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → SlowCalibratedConditions P ε := by
  have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    (tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 0) (𝓝 0)).mono_left nhdsWithin_le_nhds
  have hc := hid.eventually (eventually_le_nhds
    (div_pos (mul_pos slowBiasConstant_pos (slowModelScale_pos P)) (by norm_num : (0:ℝ)<256)))
  have ha := ((slow_amplitude_tendsto P).const_mul 160).eventually
    (eventually_le_nhds (show (160:ℝ)*0 < P.gap by simpa using P.gap_pos))
  have hg : Tendsto (fun ε : ℝ =>
      slowPopulationGradientConstant*Real.sqrt (P.gap/(10*firstOrderGradientConstant))*Real.sqrt ε)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.sqrt_zero,mul_zero] using
      ((Real.continuous_sqrt.tendsto 0).comp hid).const_mul
        (slowPopulationGradientConstant*Real.sqrt (P.gap/(10*firstOrderGradientConstant)))
  have hG := hg.eventually (eventually_le_nhds P.gradientBound_pos)
  have he : ∀ᶠ ε : ℝ in 𝓝[>] 0, SlowCalibratedConditions P ε := by
    filter_upwards [self_mem_nhdsWithin,hc,ha,hG] with ε hε hc ha hg
    exact ⟨hε,hc,ha,hg⟩
  obtain ⟨ε₀,hε₀,hh⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp he
  exact ⟨ε₀,hε₀,fun ε hε hs => hh ⟨hε,hs⟩⟩

theorem SlowCalibratedConditions.radius_large {P : Parameters} {ε : ℝ}
    (hc : SlowCalibratedConditions P ε) : 256 ≤ slowCoefficientRadius P ε := by
  apply (le_div_iff₀ hc.tolerance_pos).mpr
  linarith [hc.coefficient_small]

theorem SlowCalibratedConditions.chain_budget {P : Parameters} {ε : ℝ}
    (hc : SlowCalibratedConditions P ε) :
    slowAmplitude (slowBlockSize P ε) ε*(slowLinks P ε+1:ℕ) ≤ P.gap/40 := by
  have hA := slowAmplitude_pos (slowBlockSize_pos P hc.tolerance_pos) hc.tolerance_pos
  have hh := firstOrderBudgetLinks_gap (Δ := P.gap) hA (by linarith [hc.amplitude_small])
  change 20*slowAmplitude (slowBlockSize P ε) ε*(slowLinks P ε+1:ℕ) ≤ P.gap/2 at hh
  linarith only [hh]

/-- Every model field for the paper's concrete logarithmic-dimensional slow
family; all scale inequalities have been discharged. -/
theorem calibrated_slow_sample_admissible (P : Parameters) {ε : ℝ}
    (hc : SlowCalibratedConditions P ε)
    (Θ : Fin (slowLinks P ε+1) → Fin (slowBlockSize P ε) → Bool) :
    Admissible
      (firstOrderChainCoefficientLaw Θ (slowCoefficientRadius P ε)
        (by linarith [hc.radius_large])).toMeasure P
      (scaledFirstOrderPopulation Θ (slowAmplitude (slowBlockSize P ε) ε)
        (slowDilation (slowBlockSize P ε)))
      (scaledFirstOrderSample Θ (slowAmplitude (slowBlockSize P ε) ε)
        (slowDilation (slowBlockSize P ε))) 0 := by
  have hd := slowBlockSize_pos P hc.tolerance_pos
  have hA := slowAmplitude_pos hd hc.tolerance_pos
  have hs : ε ≤ slowBiasConstant*slowModelScale P/2 := by
    have hb := mul_pos slowBiasConstant_pos (slowModelScale_pos P)
    linarith [hc.coefficient_small]
  have hbud := slow_four_sample_budgets P hd hc.tolerance_pos hs
  apply slow_sample_admissible P Θ hd hA.le (slowCoefficientRadius P ε)
    (by linarith [hc.radius_large])
  · have hh := hc.chain_budget
    nlinarith only [hh,P.gap_pos]
  · exact hbud.1
  · exact hbud.2.1
  · exact hbud.2.2.1
  · exact hbud.2.2.2
  · exact (slow_global_gradient_scale P hd hc.tolerance_pos (slowLinks P ε+1)
      hc.chain_budget).trans hc.population_small

end
end SampleReuse
