import SampleReuse.CurvatureFrameCore

open SecondOrder

namespace SampleReuse
noncomputable section

def curvatureKappa : ℝ := 8/Real.exp (-(9:ℝ)/4)
def curvatureSpatialScale (K γ : ℝ) : ℝ := K*γ
def curvatureAmplitude (K γ : ℝ) : ℝ := curvatureKappa*γ*(K*γ)^2
def curvatureInputDilation (K γ : ℝ) : ℝ := (K*γ)⁻¹
def curvatureCoreConstant : ℝ := 17*curvatureScalarConstant^2

theorem curvatureKappa_pos : 0 < curvatureKappa := by
  unfold curvatureKappa
  positivity

theorem curvatureCoreConstant_pos : 0 < curvatureCoreConstant := by
  have hC : 0 < curvatureScalarConstant := zero_lt_one.trans_le curvatureScalarConstant_ge_one
  unfold curvatureCoreConstant
  positivity

theorem curvatureAmplitude_pos {K γ : ℝ} (hK : 0 < K) (hγ : 0 < γ) :
    0 < curvatureAmplitude K γ := by
  have hκ := curvatureKappa_pos
  unfold curvatureAmplitude
  positivity

theorem curvatureInputDilation_pos {K γ : ℝ} (hK : 0 < K) (hγ : 0 < γ) :
    0 < curvatureInputDilation K γ := by
  unfold curvatureInputDilation
  positivity

theorem curvature_scale_two {K γ : ℝ} (hK : 0 < K) (hγ : 0 < γ) :
    curvatureAmplitude K γ*(curvatureInputDilation K γ)^2 = curvatureKappa*γ := by
  unfold curvatureAmplitude curvatureInputDilation
  field_simp

theorem curvature_scale_three {K γ : ℝ} (hK : 0 < K) (hγ : 0 < γ) :
    curvatureAmplitude K γ*(curvatureInputDilation K γ)^3 = curvatureKappa/K := by
  unfold curvatureAmplitude curvatureInputDilation
  field_simp
  ring

theorem curvature_scale_negative {K γ : ℝ} (hK : 0 < K) (hγ : 0 < γ) :
    curvatureAmplitude K γ*(curvatureInputDilation K γ)^2*Real.exp (-(9:ℝ)/4) = 8*γ := by
  rw [curvature_scale_two hK hγ]
  unfold curvatureKappa
  field_simp

theorem curvature_scale_gradient {K γ Δ : ℝ} (hK : 0 < K) (hγ : 0 < γ)
    (hΔ : 0 ≤ Δ) (n : ℕ) (hn : curvatureAmplitude K γ*n ≤ Δ/8) :
    curvatureAmplitude K γ*curvatureInputDilation K γ*Real.sqrt n ≤
      Real.sqrt (curvatureKappa*Δ/8)*Real.sqrt γ := by
  let A := curvatureAmplitude K γ
  let β := curvatureInputDilation K γ
  have hA : 0 < A := curvatureAmplitude_pos hK hγ
  have hβ : 0 < β := curvatureInputDilation_pos hK hγ
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
  have hsq : (A*β*Real.sqrt n)^2 = (curvatureKappa*γ)*(A*n) := by
    have he := curvature_scale_two hK hγ
    change A*β^2 = curvatureKappa*γ at he
    calc
      _ = (A*β^2)*(A*n) := by rw [mul_pow,mul_pow,hs]; ring
      _ = _ := by rw [he]
  have hright : (Real.sqrt (curvatureKappa*Δ/8)*Real.sqrt γ)^2 = curvatureKappa*γ*(Δ/8) := by
    rw [mul_pow,Real.sq_sqrt
      (div_nonneg (mul_nonneg curvatureKappa_pos.le hΔ) (by norm_num)),Real.sq_sqrt hγ.le]
    ring
  have hm := mul_le_mul_of_nonneg_left hn (mul_nonneg curvatureKappa_pos.le hγ.le)
  have hnonneg : 0 ≤ Real.sqrt (curvatureKappa*Δ/8)*Real.sqrt γ := by positivity
  change A*β*Real.sqrt n ≤ _
  nlinarith only [hsq,hright,hm,hnonneg,
    sq_nonneg (Real.sqrt (curvatureKappa*Δ/8)*Real.sqrt γ-A*β*Real.sqrt n)]

theorem scaled_frame_core_derivative_rates {d T : ℕ}
    (U : Point (T+1) →ₗᵢ[ℝ] Point d) {K γ Δ : ℝ}
    (hK : 0 < K) (hγ : 0 < γ) (hΔ : 0 ≤ Δ)
    (hn : curvatureAmplitude K γ*(T+1:ℕ) ≤ Δ/8) (x : Point d) :
    ‖gradient (curvatureFrameCore U (curvatureAmplitude K γ) (curvatureInputDilation K γ)) x‖ ≤
      (curvatureCoreConstant*Real.sqrt (curvatureKappa*Δ/8))*Real.sqrt γ ∧
    ‖hessian (curvatureFrameCore U (curvatureAmplitude K γ) (curvatureInputDilation K γ)) x‖ ≤
      curvatureKappa*curvatureCoreConstant*γ ∧
    ‖iteratedFDeriv ℝ 3 (curvatureFrameCore U (curvatureAmplitude K γ) (curvatureInputDilation K γ)) x‖ ≤
      curvatureKappa/K*curvatureCoreConstant := by
  have hA := (curvatureAmplitude_pos hK hγ).le
  have hβ := (curvatureInputDilation_pos hK hγ).le
  refine ⟨?_,?_,?_⟩
  · have hh := curvatureFrameCore_gradient_bound U hA hβ x
    have hs := mul_le_mul_of_nonneg_left (curvature_scale_gradient hK hγ hΔ (T+1) hn)
      curvatureCoreConstant_pos.le
    dsimp [curvatureCoreConstant] at hs ⊢
    nlinarith only [hh,hs]
  · have hh := curvatureFrameCore_hessian_bound U hA hβ x
    rw [curvature_scale_two hK hγ] at hh
    convert hh using 1
    unfold curvatureCoreConstant
    ring
  · have hh := curvatureFrameCore_iterated_bound U hA hβ 3 (Or.inr rfl) x
    rw [curvature_scale_three hK hγ] at hh
    exact hh

end
end SampleReuse
