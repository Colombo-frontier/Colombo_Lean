import SampleReuse.CurvatureCalibration

open Filter
open scoped Topology

namespace SampleReuse
noncomputable section

def curvatureChainLength (P : Parameters) (γ : ℝ) : ℕ :=
  ⌊P.gap/(8*curvatureAmplitude (curvatureScaleK P) γ)⌋₊

def curvatureLengthConstant (P : Parameters) : ℝ :=
  P.gap/(16*curvatureKappa*(curvatureScaleK P)^2)

theorem curvatureLengthConstant_pos (P : Parameters) : 0 < curvatureLengthConstant P := by
  have hK := curvatureScaleK_pos P
  have hκ := curvatureKappa_pos
  have hΔ := P.gap_pos
  unfold curvatureLengthConstant
  positivity

theorem floor_half_bound {x : ℝ} (hx : 2 ≤ x) :
    1 ≤ ⌊x⌋₊ ∧ x/2 ≤ (⌊x⌋₊ : ℝ) ∧ (⌊x⌋₊ : ℝ) ≤ x := by
  have hn : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr (by linarith)
  have hn' : (1:ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hn
  exact ⟨hn,by linarith [Nat.lt_floor_add_one x],Nat.floor_le (by linarith)⟩

theorem curvature_chain_length_bounds (P : Parameters) {γ : ℝ} (hγ : 0 < γ)
    (hsmall : curvatureAmplitude (curvatureScaleK P) γ ≤ P.gap/16) :
    1 ≤ curvatureChainLength P γ ∧
    curvatureAmplitude (curvatureScaleK P) γ*(curvatureChainLength P γ : ℕ) ≤ P.gap/8 ∧
    curvatureLengthConstant P/γ^3 ≤ (curvatureChainLength P γ : ℝ) ∧
    (curvatureChainLength P γ : ℝ) ≤ 2*curvatureLengthConstant P/γ^3 := by
  have hK := curvatureScaleK_pos P
  have hA := curvatureAmplitude_pos hK hγ
  have hκ := curvatureKappa_pos
  have hx : 2 ≤ P.gap/(8*curvatureAmplitude (curvatureScaleK P) γ) :=
    (le_div_iff₀ (mul_pos (by norm_num) hA)).mpr (by linarith)
  have hh := floor_half_bound hx
  change 1 ≤ curvatureChainLength P γ ∧
    P.gap/(8*curvatureAmplitude (curvatureScaleK P) γ)/2 ≤ (curvatureChainLength P γ : ℝ) ∧
    (curvatureChainLength P γ : ℝ) ≤ P.gap/(8*curvatureAmplitude (curvatureScaleK P) γ) at hh
  refine ⟨hh.1,?_,?_,?_⟩
  · have hm := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<8) hA)).mp hh.2.2
    nlinarith only [hm]
  · convert hh.2.1 using 1
    unfold curvatureLengthConstant curvatureAmplitude
    field_simp
    ring_nf
    simp
  · convert hh.2.2 using 1
    unfold curvatureLengthConstant curvatureAmplitude
    field_simp
    ring_nf

theorem curvature_small_amplitude (P : Parameters) :
    ∃ η : ℝ, 0 < η ∧ ∀ γ : ℝ, 0 < γ → γ < η →
      curvatureAmplitude (curvatureScaleK P) γ ≤ P.gap/16 := by
  have hc : Continuous (curvatureAmplitude (curvatureScaleK P)) := by
    unfold curvatureAmplitude
    fun_prop
  have he : ∀ᶠ γ in 𝓝 (0:ℝ), curvatureAmplitude (curvatureScaleK P) γ < P.gap/16 :=
    hc.continuousAt.eventually (gt_mem_nhds (by
      simpa [curvatureAmplitude] using (div_pos P.gap_pos (by norm_num : (0:ℝ)<16))))
  obtain ⟨η,hη,hh⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨η,hη,fun γ hγ hγη => (hh ?_).le⟩
  simpa only [Real.dist_eq,sub_zero,abs_of_pos hγ] using hγη

end
end SampleReuse
