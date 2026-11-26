import SecondOrder.CurvatureHolderAsymptotics

open Filter
open scoped Topology

namespace SecondOrder
noncomputable section

def curvatureHolderInverseSquareConstant (L ν : ℝ) : ℝ :=
  (32*curvatureGeometryConstant)^(2/ν)/L^(2/ν)

theorem curvatureHolderInverseSquareConstant_pos {L ν : ℝ} (hL : 0<L) :
    0<curvatureHolderInverseSquareConstant L ν := by
  have hG := curvatureGeometryConstant_pos
  unfold curvatureHolderInverseSquareConstant
  positivity

theorem curvatureHolder_inverse_square {L γ ν : ℝ} (hL : 0<L) (hγ : 0<γ) :
    curvatureHolderInverseSquareConstant L ν*γ^(2/ν)=1/(curvatureHolderInputScale L γ ν)^2 := by
  rw [curvatureHolderInputScale_sq hL hγ]
  unfold curvatureHolderInverseSquareConstant
  simp only [one_div,inv_div]
  ring

theorem curvatureHolderOutputScale_eq {D L γ ν : ℝ} (hL : 0<L) (hγ : 0<γ) :
    curvatureOutputScale D (curvatureHolderEffectiveL L γ ν) γ=
      8*curvatureHolderInverseSquareConstant L ν*(D*γ^(1+2/ν)) := by
  unfold curvatureOutputScale
  rw [curvatureHolderInputScale_identity hγ,Real.rpow_add hγ,Real.rpow_one]
  rw [show 8*curvatureHolderInverseSquareConstant L ν*(D*(γ*γ^(2/ν)))=
      8*D*γ*(curvatureHolderInverseSquareConstant L ν*γ^(2/ν)) by ring,
    curvatureHolder_inverse_square hL hγ]
  ring

theorem curvatureHolder_gradient_noise_of_squared {D L σ g γ ν : ℝ}
    (hD : 0≤D) (hL : 0<L) (hσ : 0≤σ) (hg : 0≤g) (hγ : 0<γ)
    (h : σ^2*curvatureHolderInverseSquareConstant L ν*(D*γ^(2/ν))≤g^2) :
    σ*Real.sqrt D≤g*curvatureHolderInputScale L γ ν := by
  have hβ := curvatureHolderInputScale_pos (ν := ν) hL hγ
  have he : σ^2*curvatureHolderInverseSquareConstant L ν*(D*γ^(2/ν))=
      σ^2*D/(curvatureHolderInputScale L γ ν)^2 := by
    rw [show σ^2*curvatureHolderInverseSquareConstant L ν*(D*γ^(2/ν))=
      σ^2*D*(curvatureHolderInverseSquareConstant L ν*γ^(2/ν)) by ring,
      curvatureHolder_inverse_square hL hγ]
    ring
  rw [he] at h
  have hh := (div_le_iff₀ (sq_pos_of_pos hβ)).1 h
  apply (sq_le_sq₀ (mul_nonneg hσ (Real.sqrt_nonneg D)) (mul_nonneg hg hβ.le)).1
  simpa only [mul_pow,Real.sq_sqrt hD] using hh

theorem curvatureHolder_stage_of_squared {D σ γ : ℝ} (hγ : 0<γ)
    (h : 134217728*curvatureNoiseConstant^2*(D*γ^2)≤σ^2) :
    131072*D≤(curvatureCoefficientScale σ γ)^2 := by
  have hC : 0<curvatureNoiseConstant := lt_of_lt_of_le (by norm_num) curvatureNoiseConstant_bounds.1
  unfold curvatureCoefficientScale
  rw [div_pow]
  apply (le_div_iff₀ (sq_pos_of_pos (show 0<32*curvatureNoiseConstant*γ by positivity))).2
  nlinarith only [h]

/-- Fixing positive model parameters and 0<ν≤1, all the actual finite
construction conditions hold for every sufficiently small positive γ. -/
theorem curvatureHolderConditions_eventually (P : Parameters) {ν : ℝ} (hν : 0<ν) (hν1 : ν≤1) :
    ∀ᶠ γ : ℝ in 𝓝[>] 0, CurvatureHolderConditions P γ ν := by
  let σ := curvatureNoiseBudget P
  let c := curvatureHolderInverseSquareConstant P.hessianHolder ν
  have hσ : 0<σ := curvatureNoiseBudget_pos P
  have hp : 0<2/ν := div_pos (by norm_num) hν
  have hid : Tendsto (fun γ : ℝ => γ) (𝓝[>] 0) (𝓝 0) :=
    (tendsto_id : Tendsto (fun γ : ℝ => γ) (𝓝 0) (𝓝 0)).mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ γ : ℝ in 𝓝[>] 0, 64*curvatureNoiseConstant*γ≤σ := by
    have hh : Tendsto (fun γ : ℝ => 64*curvatureNoiseConstant*γ) (𝓝[>] 0) (𝓝 0) := by
      simpa using hid.const_mul (64*curvatureNoiseConstant)
    exact hh.eventually (eventually_le_nhds hσ)
  have hLip : ∀ᶠ γ : ℝ in 𝓝[>] 0, 8*curvatureGeometryConstant*γ≤P.gradientLip := by
    have hh : Tendsto (fun γ : ℝ => 8*curvatureGeometryConstant*γ) (𝓝[>] 0) (𝓝 0) := by
      simpa using hid.const_mul (8*curvatureGeometryConstant)
    exact hh.eventually (eventually_le_nhds P.gradientLip_pos)
  have hgrad : ∀ᶠ γ : ℝ in 𝓝[>] 0, σ^2*c*
      ((curvatureHolderBlockSize P.gap P.hessianHolder σ γ ν:ℝ)*γ^(2/ν))≤P.gradientNoise^2 := by
    have hh : Tendsto (fun γ : ℝ => σ^2*c*
      ((curvatureHolderBlockSize P.gap P.hessianHolder σ γ ν:ℝ)*γ^(2/ν))) (𝓝[>] 0) (𝓝 0) := by
      simpa using (curvatureHolderBlockSize_mul_rpow_tendsto (σ := σ) P.gap_pos.le P.hessianHolder_pos hν hν1 hp).const_mul (σ^2*c)
    exact hh.eventually (eventually_le_nhds (sq_pos_of_pos P.gradientNoise_pos))
  have hgap : ∀ᶠ γ : ℝ in 𝓝[>] 0, 64*c*
      ((curvatureHolderBlockSize P.gap P.hessianHolder σ γ ν:ℝ)*γ^(1+2/ν))≤P.gap := by
    have hh : Tendsto (fun γ : ℝ => 64*c*
      ((curvatureHolderBlockSize P.gap P.hessianHolder σ γ ν:ℝ)*γ^(1+2/ν))) (𝓝[>] 0) (𝓝 0) := by
      simpa using (curvatureHolderBlockSize_mul_rpow_tendsto (σ := σ) P.gap_pos.le P.hessianHolder_pos hν hν1
        (show 0<1+2/ν by linarith only [hp])).const_mul (64*c)
    exact hh.eventually (eventually_le_nhds P.gap_pos)
  have hstage : ∀ᶠ γ : ℝ in 𝓝[>] 0, 134217728*curvatureNoiseConstant^2*
      ((curvatureHolderBlockSize P.gap P.hessianHolder σ γ ν:ℝ)*γ^2)≤σ^2 := by
    have hh : Tendsto (fun γ : ℝ => 134217728*curvatureNoiseConstant^2*
      ((curvatureHolderBlockSize P.gap P.hessianHolder σ γ ν:ℝ)*γ^2)) (𝓝[>] 0) (𝓝 0) := by
      simpa only [Real.rpow_natCast,mul_zero] using
        (curvatureHolderBlockSize_mul_rpow_tendsto (σ := σ) P.gap_pos.le P.hessianHolder_pos hν hν1
          (show (0:ℝ)<(2:ℕ) by norm_num)).const_mul (134217728*curvatureNoiseConstant^2)
    exact hh.eventually (eventually_le_nhds (sq_pos_of_pos hσ))
  filter_upwards [self_mem_nhdsWithin,hsmall,hLip,hgrad,hgap,hstage] with γ hγ hs hl hg ha ht
  refine ⟨hγ,hν,hν1,hs,hl,?_,?_,curvatureHolder_stage_of_squared hγ ht⟩
  · exact curvatureHolder_gradient_noise_of_squared (Nat.cast_nonneg _) P.hessianHolder_pos hσ.le P.gradientNoise_pos.le hγ hg
  · rw [curvatureHolderOutputScale_eq P.hessianHolder_pos hγ]
    convert ha using 1 <;> ring

theorem curvatureHolderConditions_small (P : Parameters) {ν : ℝ} (hν : 0<ν) (hν1 : ν≤1) :
    ∃ γ₀ : ℝ, 0<γ₀ ∧ ∀ γ : ℝ, 0<γ → γ≤γ₀ → CurvatureHolderConditions P γ ν := by
  obtain ⟨γ₀,hγ₀,hh⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp (curvatureHolderConditions_eventually P hν hν1)
  exact ⟨γ₀,hγ₀,fun γ hγ hsmall => hh ⟨hγ,hsmall⟩⟩

end
end SecondOrder
