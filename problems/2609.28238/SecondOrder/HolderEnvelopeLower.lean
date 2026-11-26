import SecondOrder.HardDimensions

open Filter
open scoped Topology ENNReal

namespace SecondOrder
noncomputable section

theorem curvatureHvpDimension_normalized_tendsto (P : Parameters) {ν κ : ℝ}
    (hν : 0<ν) (hν1 : ν≤1) (hκ : 1+2/ν<κ) :
    Tendsto (fun γ : ℝ => (curvatureHvpDimension P γ ν:ℝ)*γ^κ) (𝓝[>] 0) (𝓝 0) := by
  let c := P.gap*P.hessianHolder^(2/ν)/(16*(32*curvatureGeometryConstant)^(2/ν))
  have hp : Tendsto (fun γ : ℝ => γ^(κ-(1+2/ν))) (𝓝[>] 0) (𝓝 0) := by
    have hr : 0<κ-(1+2/ν) := sub_pos.mpr hκ
    simpa only [Real.zero_rpow hr.ne'] using
      (Real.continuousAt_rpow_const 0 (κ-(1+2/ν)) (.inr hr.le)).tendsto.mono_left nhdsWithin_le_nhds
  have hup : Tendsto (fun γ : ℝ => c*γ^(κ-(1+2/ν))) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using hp.const_mul c
  apply squeeze_zero' _ _ hup
  · filter_upwards [self_mem_nhdsWithin] with γ hγ
    exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (show 0≤γ from le_of_lt hγ) _)
  · filter_upwards [self_mem_nhdsWithin,curvatureHolderConditions_eventually P hν hν1] with γ hγ hc
    have hh := mul_le_mul_of_nonneg_right (curvatureHolderEndpoint_dimension P hc)
      (Real.rpow_nonneg (show 0≤γ from le_of_lt hγ) κ)
    change (curvatureHvpDimension P γ ν:ℝ)*γ^κ≤_ at hh
    apply hh.trans_eq
    rw [Real.rpow_sub hγ]
    dsimp [c]
    ring

/-- The actual hard dimensions fit the exact dimension envelope in the
manuscript, uniformly for both independently small tolerances. -/
theorem holderHardDimensions_fit_small (P : Parameters) {ν κ : ℝ}
    (hν : 0<ν) (hν1 : ν≤1) (hκ : 1+2/ν<κ) :
    ∃ ε₀ γ₀ : ℝ, 0<ε₀ ∧ 0<γ₀ ∧ ∀ ε γ : ℝ, 0<ε → ε≤ε₀ → 0<γ → γ≤γ₀ →
      FirstOrderHolderConditions P ε ν ∧ CurvatureHolderConditions P γ ν ∧
      firstOrderHvpDimension P ε≤toleranceDimensionEnvelope κ ε γ ∧
      curvatureHvpDimension P γ ν≤toleranceDimensionEnvelope κ ε γ := by
  have hκ1 : 1<κ := by have hh := div_pos (by norm_num : (0:ℝ)<2) hν; linarith only [hκ,hh]
  have hκ0 : 0≤κ := by linarith only [hκ1]
  have he := (firstOrderHvpDimension_normalized_tendsto P hν hν1 hκ1).eventually
    (eventually_le_nhds (show (0:ℝ)<1 by norm_num))
  have hg := (curvatureHvpDimension_normalized_tendsto P hν hν1 hκ).eventually
    (eventually_le_nhds (show (0:ℝ)<1 by norm_num))
  have hle : ∀ᶠ x : ℝ in 𝓝[>] 0, x≤1 :=
    (eventually_le_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds
  have hevent : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      FirstOrderHolderConditions P ε ν ∧ (firstOrderHvpDimension P ε:ℝ)*ε^κ≤1 ∧ ε≤1 := by
    filter_upwards [firstOrderHolderConditions_eventually P hν hν1,he,hle] with ε hc hh h1
    exact ⟨hc,hh,h1⟩
  have hgevent : ∀ᶠ γ : ℝ in 𝓝[>] 0,
      CurvatureHolderConditions P γ ν ∧ (curvatureHvpDimension P γ ν:ℝ)*γ^κ≤1 ∧ γ≤1 := by
    filter_upwards [curvatureHolderConditions_eventually P hν hν1,hg,hle] with γ hc hh h1
    exact ⟨hc,hh,h1⟩
  obtain ⟨ε₀,hε₀,he₀⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hevent
  obtain ⟨γ₀,hγ₀,hg₀⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hgevent
  refine ⟨ε₀,γ₀,hε₀,hγ₀,?_⟩
  intro ε γ hε hεsmall hγ hγsmall
  obtain ⟨hce,hdε,hε1⟩ := he₀ ⟨hε,hεsmall⟩
  obtain ⟨hcg,hdγ,hγ1⟩ := hg₀ ⟨hγ,hγsmall⟩
  exact ⟨hce,hcg,dimension_le_toleranceEnvelope_left hκ0 hε hγ hγ1 hdε,
    dimension_le_toleranceEnvelope_right hκ0 hε hε1 hγ hdγ⟩

/-- Quantitative minimax lower frontier on the manuscript's exact supremum
over 1≤d≤ceil((epsilon*gamma)^(-kappa)). -/
theorem holderEnvelope_minimax_lower_small (P : Parameters) {ν κ : ℝ}
    (hν : 0<ν) (hν1 : ν≤1) (hκ : 1+2/ν<κ) :
    ∃ ε₀ γ₀ : ℝ, 0<ε₀ ∧ 0<γ₀ ∧ ∀ ε γ : ℝ, 0<ε → ε≤ε₀ → 0<γ → γ≤γ₀ →
      ENNReal.ofReal ((firstOrderEndpointThreshold P.gap (firstOrderHolderNoiseBudget P) ε+
        curvatureHolderThreshold P.gap P.hessianHolder (curvatureNoiseBudget P)
          (curvatureHolderBlockSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν) γ ν)/2)≤
        hvpEnvelopeComplexity P ν κ ε γ := by
  obtain ⟨ε₀,γ₀,hε₀,hγ₀,hfit⟩ := holderHardDimensions_fit_small P hν hν1 hκ
  refine ⟨ε₀,γ₀,hε₀,hγ₀,?_⟩
  intro ε γ hε hεsmall hγ hγsmall
  obtain ⟨hce,hcg,hde,hdg⟩ := hfit ε γ hε hεsmall hγ hγsmall
  exact hvpEnvelopeComplexity_two_lower P ν κ ε γ (firstOrderHvpDimension P ε) (curvatureHvpDimension P γ ν)
    (firstOrderHvpDimension_pos P hε) (curvatureHvpDimension_pos P hγ ν) hde hdg _ _
    (firstOrderHvp_minimax_lower P hce γ) (curvatureHvp_minimax_lower P hcg ε)

end
end SecondOrder
