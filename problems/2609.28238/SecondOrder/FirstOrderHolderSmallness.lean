import SecondOrder.FirstOrderHolderQueryLower

open Filter
open scoped Topology

namespace SecondOrder
noncomputable section

theorem firstOrderEndpoint_sqrt_tendsto {Δ s : ℝ} (hΔ : 0≤Δ) :
    Tendsto (fun ε : ℝ => ε*Real.sqrt (firstOrderEndpointBlockSize Δ s ε)) (𝓝[>] 0) (𝓝 0) := by
  have hh : Tendsto (fun ε : ℝ => (firstOrderEndpointBlockSize Δ s ε:ℝ)*ε^2) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_natCast] using firstOrderEndpointBlockSize_mul_rpow_tendsto
      (s := s) hΔ (show (0:ℝ)<(2:ℕ) by norm_num)
  have he : (fun ε : ℝ => ε*Real.sqrt (firstOrderEndpointBlockSize Δ s ε)) =ᶠ[𝓝[>] 0]
      (fun ε : ℝ => Real.sqrt ((firstOrderEndpointBlockSize Δ s ε:ℝ)*ε^2)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [Real.sqrt_mul (Nat.cast_nonneg _),Real.sqrt_sq_eq_abs,abs_of_pos hε,mul_comm]
  apply (tendsto_congr' he).mpr
  simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hh

theorem firstOrderHolderCoefficient_tendsto (P : Parameters) {ν : ℝ} (hν : 0<ν) (hν1 : ν≤1) :
    Tendsto (fun ε : ℝ => firstOrderHolderCoefficient P ε ν) (𝓝[>] 0) (𝓝 0) := by
  have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    (tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 0) (𝓝 0)).mono_left nhdsWithin_le_nhds
  have hA : Tendsto (fun ε : ℝ => 2*(firstOrderOutputScale ε*firstOrderGeometryConstant)) (𝓝[>] 0) (𝓝 0) := by
    have hh := hid.const_mul (8*firstOrderGeometryConstant/firstOrderGradientConstant)
    simp only [mul_zero] at hh
    convert hh using 1
    ext ε
    unfold firstOrderOutputScale
    ring
  have hH : Tendsto (fun ε : ℝ => firstOrderOutputScale ε*(firstOrderGeometryConstant*
      Real.sqrt (firstOrderEndpointBlockSize P.gap (firstOrderHolderNoiseBudget P) ε))) (𝓝[>] 0) (𝓝 0) := by
    have hh := (firstOrderEndpoint_sqrt_tendsto (s := firstOrderHolderNoiseBudget P) P.gap_pos.le).const_mul
      (4*firstOrderGeometryConstant/firstOrderGradientConstant)
    simp only [mul_zero] at hh
    convert hh using 1
    ext ε
    unfold firstOrderOutputScale
    ring
  have hpowA := (Real.continuousAt_rpow_const 0 (1-ν) (.inr (sub_nonneg.mpr hν1))).tendsto.comp hA
  have hpowH := (Real.continuousAt_rpow_const 0 ν (.inr hν.le)).tendsto.comp hH
  simpa only [Real.zero_rpow hν.ne',mul_zero,firstOrderHolderCoefficient] using hpowA.mul hpowH

theorem firstOrderHolderConditions_eventually (P : Parameters) {ν : ℝ} (hν : 0<ν) (hν1 : ν≤1) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, FirstOrderHolderConditions P ε ν := by
  have hc := firstOrderEndpointConditions_eventually P P.gradientNoise_pos
  have hH := (firstOrderHolderCoefficient_tendsto P hν hν1).eventually
    (eventually_le_nhds P.hessianHolder_pos)
  filter_upwards [hc,hH] with ε hc hh
  have hs := firstOrderEndpoint_smallness P P.gradientNoise_pos
    (Nat.cast_nonneg (firstOrderEndpointBlockSize P.gap (firstOrderHolderNoiseBudget P) ε))
    hc.tolerance_pos hc.gradient_small hc.noise_small hc.hessian_small hc.gap_large
  exact ⟨hc.tolerance_pos,hν,hν1,hs.1,hs.2.1,hh,hs.2.2.2.1,hs.2.2.2.2⟩

theorem firstOrderHolderConditions_small (P : Parameters) {ν : ℝ} (hν : 0<ν) (hν1 : ν≤1) :
    ∃ ε₀ : ℝ, 0<ε₀ ∧ ∀ ε : ℝ, 0<ε → ε≤ε₀ → FirstOrderHolderConditions P ε ν := by
  obtain ⟨ε₀,hε₀,hh⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp (firstOrderHolderConditions_eventually P hν hν1)
  exact ⟨ε₀,hε₀,fun ε hε hsmall => hh ⟨hε,hsmall⟩⟩

end
end SecondOrder
