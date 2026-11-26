import SecondOrder.ScaledCurvatureModel
import SecondOrder.Rates

namespace SecondOrder
noncomputable section

def curvatureInputScale (L γ : ℝ) : ℝ := L/(16*curvatureGeometryConstant*γ)
def curvatureOutputScale (D L γ : ℝ) : ℝ := 8*D*γ/(curvatureInputScale L γ)^2
def curvatureCoefficientScale (σ γ : ℝ) : ℝ := σ/(32*curvatureNoiseConstant*γ)

theorem curvatureInputScale_pos {L γ : ℝ} (hL : 0<L) (hγ : 0<γ) : 0<curvatureInputScale L γ :=
  div_pos hL (mul_pos (mul_pos (by norm_num) curvatureGeometryConstant_pos) hγ)

theorem curvatureOutputScale_pos {D L γ : ℝ} (hD : 0<D) (hL : 0<L) (hγ : 0<γ) :
    0<curvatureOutputScale D L γ :=
  div_pos (by positivity) (sq_pos_of_pos (curvatureInputScale_pos hL hγ))

theorem curvatureScales_identities {D L γ : ℝ} (hD : 0<D) (hL : 0<L) (hγ : 0<γ) :
    curvatureOutputScale D L γ*(curvatureInputScale L γ)^2/D=8*γ ∧
    curvatureOutputScale D L γ*(curvatureInputScale L γ)^3*curvatureGeometryConstant/D=L/2 ∧
    curvatureOutputScale D L γ=2048*curvatureGeometryConstant^2*D*γ^3/L^2 :=
  curvature_scale_lipschitz hL.ne' curvatureGeometryConstant_pos.ne' hγ.ne' hD.ne'

theorem curvatureScales_smoothness {D L γ : ℝ} (hD : 0<D) (hL : 0<L) (hγ : 0<γ) :
    curvatureOutputScale D L γ*(curvatureInputScale L γ)^2*(curvatureGeometryConstant/D)=
      8*curvatureGeometryConstant*γ ∧
    curvatureOutputScale D L γ*(curvatureInputScale L γ)^3*(curvatureGeometryConstant/D)=L/2 := by
  have hh := curvatureScales_identities hD hL hγ
  constructor
  · calc
      _ = (curvatureOutputScale D L γ*(curvatureInputScale L γ)^2/D)*curvatureGeometryConstant := by ring
      _ = _ := by rw [hh.1]; ring
  · convert hh.2.1 using 1 <;> ring

theorem curvatureCoefficientScale_ge_two {σ γ : ℝ} (hγ : 0<γ)
    (hsmall : 64*curvatureNoiseConstant*γ≤σ) : 2≤curvatureCoefficientScale σ γ := by
  have hC : 0<curvatureNoiseConstant := lt_of_lt_of_le (by norm_num) curvatureNoiseConstant_bounds.1
  apply (le_div_iff₀ (by positivity : 0<32*curvatureNoiseConstant*γ)).2
  nlinarith only [hsmall]

theorem curvatureScales_hessian_noise {D L σ γ : ℝ} (hD : 0<D) (hL : 0<L) (hγ : 0<γ)
    (hsmall : 64*curvatureNoiseConstant*γ≤σ) :
    curvatureOutputScale D L γ*(curvatureInputScale L γ)^2*
      (curvatureNoiseConstant*(curvatureCoefficientScale σ γ+1)/D)≤σ := by
  have hC : 0<curvatureNoiseConstant := lt_of_lt_of_le (by norm_num) curvatureNoiseConstant_bounds.1
  have hs := (curvatureScales_identities hD hL hγ).1
  have he : curvatureOutputScale D L γ*(curvatureInputScale L γ)^2*
      (curvatureNoiseConstant*(curvatureCoefficientScale σ γ+1)/D)=σ/4+8*curvatureNoiseConstant*γ := by
    calc
      _ = (curvatureOutputScale D L γ*(curvatureInputScale L γ)^2/D)*
        (curvatureNoiseConstant*(curvatureCoefficientScale σ γ+1)) := by ring
      _ = _ := by
        rw [hs]
        unfold curvatureCoefficientScale
        field_simp
        <;> ring
  rw [he]
  nlinarith [mul_pos hC hγ]

theorem curvatureScales_gradient_noise {D L σ γ : ℝ} (hD : 0<D) (hL : 0<L) (hγ : 0<γ)
    (hsmall : 64*curvatureNoiseConstant*γ≤σ) :
    curvatureOutputScale D L γ*curvatureInputScale L γ*
      (curvatureNoiseConstant*(curvatureCoefficientScale σ γ+1)/Real.sqrt D)≤
        16*curvatureGeometryConstant*σ*γ*Real.sqrt D/L := by
  have hβ := curvatureInputScale_pos hL hγ
  have hs := Real.sqrt_pos.2 hD
  have hsq := Real.sq_sqrt hD.le
  have hh := mul_le_mul_of_nonneg_right (curvatureScales_hessian_noise hD hL hγ hsmall)
    (div_nonneg hs.le hβ.le)
  have he : curvatureOutputScale D L γ*(curvatureInputScale L γ)^2*
      (curvatureNoiseConstant*(curvatureCoefficientScale σ γ+1)/D)*(Real.sqrt D/curvatureInputScale L γ)=
      curvatureOutputScale D L γ*curvatureInputScale L γ*
      (curvatureNoiseConstant*(curvatureCoefficientScale σ γ+1)/Real.sqrt D) := by
    field_simp
    <;> linear_combination (curvatureOutputScale D L γ*(curvatureInputScale L γ)^2*
      (curvatureNoiseConstant*(curvatureCoefficientScale σ γ+1)))*hsq
  rw [he] at hh
  apply hh.trans_eq
  unfold curvatureInputScale
  field_simp
  <;> ring

theorem curvatureScales_value_noise {D L σ γ : ℝ} (hD : 0<D) (hL : 0<L) (hγ : 0<γ)
    (hsmall : 64*curvatureNoiseConstant*γ≤σ) :
    curvatureOutputScale D L γ*(curvatureNoiseConstant*(curvatureCoefficientScale σ γ+1))≤
      256*curvatureGeometryConstant^2*D*σ*γ^2/L^2 := by
  have hβ := curvatureInputScale_pos hL hγ
  have hh := mul_le_mul_of_nonneg_right (curvatureScales_hessian_noise hD hL hγ hsmall)
    (div_nonneg hD.le (sq_nonneg (curvatureInputScale L γ)))
  have he : curvatureOutputScale D L γ*(curvatureInputScale L γ)^2*
      (curvatureNoiseConstant*(curvatureCoefficientScale σ γ+1)/D)*(D/(curvatureInputScale L γ)^2)=
      curvatureOutputScale D L γ*(curvatureNoiseConstant*(curvatureCoefficientScale σ γ+1)) := by
    field_simp
    <;> ring
  rw [he] at hh
  apply hh.trans_eq
  unfold curvatureInputScale
  field_simp
  <;> ring

end
end SecondOrder
