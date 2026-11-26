import SecondOrder.CurvatureHolderAsymptotics

open Filter
open scoped Topology

namespace SecondOrder
noncomputable section

theorem curvatureHolderEffectiveL_double {γ : ℝ} (hγ : 0<γ) (L : ℝ) :
    curvatureHolderEffectiveL (2*L) γ 1=L := by
  unfold curvatureHolderEffectiveL curvatureHolderInputScale
  norm_num only [div_one,Real.rpow_one]
  field_simp [hγ.ne',curvatureGeometryConstant_pos.ne']
  <;> ring

theorem curvatureEndpointBlockSize_holder {γ : ℝ} (hγ : 0<γ) (Δ L σ : ℝ) :
    curvatureEndpointBlockSize Δ L σ γ=curvatureHolderBlockSize Δ (2*L) σ γ 1 := by
  unfold curvatureEndpointBlockSize curvatureHolderBlockSize curvatureHolderHalfSize
  rw [curvatureHolderEffectiveL_double hγ]

theorem curvatureEndpointBlockSize_mul_rpow_tendsto {Δ L σ r : ℝ}
    (hΔ : 0≤Δ) (hL : 0<L) (hr : 0<r) :
    Tendsto (fun γ : ℝ => (curvatureEndpointBlockSize Δ L σ γ:ℝ)*γ^r) (𝓝[>] 0) (𝓝 0) := by
  have hh := curvatureHolderBlockSize_mul_rpow_tendsto (σ := σ) hΔ (show 0<2*L by positivity)
    (show (0:ℝ)<1 by norm_num) (le_refl (1:ℝ)) hr
  have he : (fun γ : ℝ => (curvatureEndpointBlockSize Δ L σ γ:ℝ)*γ^r) =ᶠ[𝓝[>] 0]
      (fun γ : ℝ => (curvatureHolderBlockSize Δ (2*L) σ γ 1:ℝ)*γ^r) := by
    filter_upwards [self_mem_nhdsWithin] with γ hγ
    rw [curvatureEndpointBlockSize_holder hγ]
  exact (tendsto_congr' he).mpr hh

theorem curvatureEndpoint_sqrt_tendsto {Δ L σ : ℝ} (hΔ : 0≤Δ) (hL : 0<L) :
    Tendsto (fun γ : ℝ => γ*Real.sqrt (curvatureEndpointBlockSize Δ L σ γ)) (𝓝[>] 0) (𝓝 0) := by
  have hh : Tendsto (fun γ : ℝ => (curvatureEndpointBlockSize Δ L σ γ:ℝ)*γ^2) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_natCast] using curvatureEndpointBlockSize_mul_rpow_tendsto
      (σ := σ) hΔ hL (show (0:ℝ)<(2:ℕ) by norm_num)
  have he : (fun γ : ℝ => γ*Real.sqrt (curvatureEndpointBlockSize Δ L σ γ)) =ᶠ[𝓝[>] 0]
      (fun γ : ℝ => Real.sqrt ((curvatureEndpointBlockSize Δ L σ γ:ℝ)*γ^2)) := by
    filter_upwards [self_mem_nhdsWithin] with γ hγ
    rw [Real.sqrt_mul (Nat.cast_nonneg _),Real.sqrt_sq_eq_abs,abs_of_pos hγ,mul_comm]
  apply (tendsto_congr' he).mpr
  simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hh

theorem curvatureEndpointConditions_eventually (P : Parameters) {σ₀ : ℝ} (hσ₀ : 0<σ₀) :
    ∀ᶠ γ : ℝ in 𝓝[>] 0, CurvatureEndpointConditions P σ₀ γ := by
  let σ := curvatureNoiseBudget P
  let c := curvatureEndpointSmallConstant
  let D := fun γ => curvatureEndpointBlockSize P.gap P.hessianHolder σ γ
  have hc : 0<c := curvatureEndpointSmallConstant_bounds.1
  have hσ : 0<σ := curvatureNoiseBudget_pos P
  have hid : Tendsto (fun γ : ℝ => γ) (𝓝[>] 0) (𝓝 0) :=
    (tendsto_id : Tendsto (fun γ : ℝ => γ) (𝓝 0) (𝓝 0)).mono_left nhdsWithin_le_nhds
  have hsqrt : Tendsto (fun γ : ℝ => γ*Real.sqrt (D γ)) (𝓝[>] 0) (𝓝 0) :=
    curvatureEndpoint_sqrt_tendsto P.gap_pos.le P.hessianHolder_pos
  have htwo : Tendsto (fun γ : ℝ => (D γ:ℝ)*γ^2) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_natCast] using curvatureEndpointBlockSize_mul_rpow_tendsto
      (σ := σ) P.gap_pos.le P.hessianHolder_pos (show (0:ℝ)<(2:ℕ) by norm_num)
  have hthree : Tendsto (fun γ : ℝ => (D γ:ℝ)*γ^3) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_natCast] using curvatureEndpointBlockSize_mul_rpow_tendsto
      (σ := σ) P.gap_pos.le P.hessianHolder_pos (show (0:ℝ)<(3:ℕ) by norm_num)
  have hgrad : Tendsto (fun γ : ℝ => σ*γ*Real.sqrt (D γ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero,mul_assoc] using hsqrt.const_mul σ
  have hvalue : Tendsto (fun γ : ℝ => (D γ:ℝ)*(σ*γ^2+γ^3)) (𝓝[>] 0) (𝓝 0) := by
    have hh := (htwo.const_mul σ).add hthree
    simp only [mul_zero,add_zero] at hh
    convert hh using 1
    ext γ
    ring
  have hl := hid.eventually (eventually_le_nhds (mul_pos hc P.gradientLip_pos))
  have hn := hsqrt.eventually (eventually_le_nhds (mul_pos hc hσ))
  have hg := hgrad.eventually (eventually_le_nhds (mul_pos hc (mul_pos P.hessianHolder_pos P.gradientNoise_pos)))
  have hv := hvalue.eventually (eventually_le_nhds (mul_pos hc (mul_pos hσ₀ (sq_pos_of_pos P.hessianHolder_pos))))
  have ha := hthree.eventually (eventually_le_nhds (mul_pos hc (mul_pos P.gap_pos (sq_pos_of_pos P.hessianHolder_pos))))
  filter_upwards [self_mem_nhdsWithin,hl,hn,hg,hv,ha] with γ hγ hl hn hg hv ha
  exact ⟨hσ₀,hγ,hl,hn,hg,hv,ha⟩

theorem curvatureEndpointConditions_small (P : Parameters) {σ₀ : ℝ} (hσ₀ : 0<σ₀) :
    ∃ γ₀ : ℝ, 0<γ₀ ∧ ∀ γ : ℝ, 0<γ → γ≤γ₀ → CurvatureEndpointConditions P σ₀ γ := by
  obtain ⟨γ₀,hγ₀,hh⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp (curvatureEndpointConditions_eventually P hσ₀)
  exact ⟨γ₀,hγ₀,fun γ hγ hsmall => hh ⟨hγ,hsmall⟩⟩

end
end SecondOrder
