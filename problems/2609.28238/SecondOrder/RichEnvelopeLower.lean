import SecondOrder.HolderEnvelopeLower
import SecondOrder.CurvatureEndpointAsymptotics

open Filter
open scoped Topology ENNReal

namespace SecondOrder
noncomputable section

theorem curvatureRichDimension_normalized_tendsto (P : Parameters) {σ₀ κ : ℝ}
    (hσ₀ : 0<σ₀) (hκ : 3<κ) :
    Tendsto (fun γ : ℝ => (curvatureRichDimension P γ:ℝ)*γ^κ) (𝓝[>] 0) (𝓝 0) := by
  let c := P.gap*P.hessianHolder^2/(4096*curvatureGeometryConstant^2)
  have hp : Tendsto (fun γ : ℝ => γ^(κ-(3:ℝ))) (𝓝[>] 0) (𝓝 0) := by
    have hr : 0<κ-(3:ℝ) := sub_pos.mpr hκ
    simpa only [Real.zero_rpow hr.ne'] using
      (Real.continuousAt_rpow_const 0 (κ-(3:ℝ)) (.inr hr.le)).tendsto.mono_left nhdsWithin_le_nhds
  have hup : Tendsto (fun γ : ℝ => c*γ^(κ-(3:ℝ))) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using hp.const_mul c
  apply squeeze_zero' _ _ hup
  · filter_upwards [self_mem_nhdsWithin] with γ hγ
    exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (show 0≤γ from le_of_lt hγ) _)
  · filter_upwards [self_mem_nhdsWithin,curvatureEndpointConditions_eventually P hσ₀] with γ hγ hc
    have hh := mul_le_mul_of_nonneg_right (curvatureEndpoint_dimension P hc)
      (Real.rpow_nonneg (show 0≤γ from le_of_lt hγ) κ)
    change (curvatureRichDimension P γ:ℝ)*γ^κ≤_ at hh
    apply hh.trans_eq
    rw [Real.rpow_sub hγ,show (3:ℝ)=(3:ℕ) by norm_num,Real.rpow_natCast]
    dsimp [c]
    ring

/-- The actual hard dimensions fit the exact dimension envelope in the
manuscript, uniformly for both independently small tolerances. -/
theorem richHardDimensions_fit_small (P : Parameters) {σ₀ κ : ℝ}
    (hσ₀ : 0<σ₀) (hκ : 3<κ) :
    ∃ ε₀ γ₀ : ℝ, 0<ε₀ ∧ 0<γ₀ ∧ ∀ ε γ : ℝ, 0<ε → ε≤ε₀ → 0<γ → γ≤γ₀ →
      FirstOrderEndpointConditions P σ₀ ε ∧ CurvatureEndpointConditions P σ₀ γ ∧
      firstOrderRichDimension P σ₀ ε≤toleranceDimensionEnvelope κ ε γ ∧
      curvatureRichDimension P γ≤toleranceDimensionEnvelope κ ε γ := by
  have hκ1 : 1<κ := by linarith only [hκ]
  have hκ0 : 0≤κ := by linarith only [hκ1]
  have he := (firstOrderRichDimension_normalized_tendsto P hσ₀ hκ1).eventually
    (eventually_le_nhds (show (0:ℝ)<1 by norm_num))
  have hg := (curvatureRichDimension_normalized_tendsto P hσ₀ hκ).eventually
    (eventually_le_nhds (show (0:ℝ)<1 by norm_num))
  have hle : ∀ᶠ x : ℝ in 𝓝[>] 0, x≤1 :=
    (eventually_le_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds
  have hevent : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      FirstOrderEndpointConditions P σ₀ ε ∧ (firstOrderRichDimension P σ₀ ε:ℝ)*ε^κ≤1 ∧ ε≤1 := by
    filter_upwards [firstOrderEndpointConditions_eventually P hσ₀,he,hle] with ε hc hh h1
    exact ⟨hc,hh,h1⟩
  have hgevent : ∀ᶠ γ : ℝ in 𝓝[>] 0,
      CurvatureEndpointConditions P σ₀ γ ∧ (curvatureRichDimension P γ:ℝ)*γ^κ≤1 ∧ γ≤1 := by
    filter_upwards [curvatureEndpointConditions_eventually P hσ₀,hg,hle] with γ hc hh h1
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
theorem richEnvelope_minimax_lower_small (P : Parameters) {σ₀ κ : ℝ}
    (hσ₀ : 0<σ₀) (hκ : 3<κ) :
    ∃ ε₀ γ₀ : ℝ, 0<ε₀ ∧ 0<γ₀ ∧ ∀ ε γ : ℝ, 0<ε → ε≤ε₀ → 0<γ → γ≤γ₀ →
      ENNReal.ofReal ((firstOrderEndpointThreshold P.gap (firstOrderNoiseBudget P σ₀) ε+
        curvatureEndpointThreshold P.gap P.hessianHolder (curvatureNoiseBudget P)
          (curvatureEndpointBlockSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ) γ)/2)≤
        richEnvelopeComplexity P σ₀ κ ε γ := by
  obtain ⟨ε₀,γ₀,hε₀,hγ₀,hfit⟩ := richHardDimensions_fit_small P hσ₀ hκ
  refine ⟨ε₀,γ₀,hε₀,hγ₀,?_⟩
  intro ε γ hε hεsmall hγ hγsmall
  obtain ⟨hce,hcg,hde,hdg⟩ := hfit ε γ hε hεsmall hγ hγsmall
  exact richEnvelopeComplexity_two_lower P σ₀ κ ε γ (firstOrderRichDimension P σ₀ ε) (curvatureRichDimension P γ)
    (firstOrderRichDimension_pos P σ₀ hε) (curvatureRichDimension_pos P hγ) hde hdg _ _
    (firstOrderRich_minimax_lower P hce γ) (curvatureRich_minimax_lower P hcg ε)

end
end SecondOrder
