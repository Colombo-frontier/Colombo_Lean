import Bilevel.PublicRadialHessian
import Bilevel.GradientJetBounds

/-! Third-derivative budget for the actual global radial extension. Decay
of the radial Hessian cancels the potentially unbounded normal coordinate. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.PublicRadialExtension
open RadialWrapper

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def thirdSlice (a R : ℝ) (e z v : E) : E →L[ℝ] E :=
  (a/R) • (((innerSL ℝ v).comp (compressDerivative R z)).smulRight e+
    ⟪e,v⟫ • compressDerivative R z+
    (innerSL ℝ e).smulRight (compressDerivative R z v)+
    ⟪e,z⟫ • RadialWrapper.hessianSlice R z v)

omit [CompleteSpace E] in
theorem hessianField_apply (a R : ℝ) (e z v : E) :
    hessianField a R e z v=(a/R) •
      (⟪compress R z,v⟫ • e+⟪e,v⟫ • compress R z+⟪e,z⟫ • compressDerivative R z v) := by
  rfl

omit [CompleteSpace E] in
theorem hessianField_slice_hasFDerivAt (a R : ℝ) (e z v : E) :
    HasFDerivAt (fun q => hessianField a R e q v) (thirdSlice a R e z v) z := by
  have hi := (innerSL ℝ v).hasFDerivAt.comp z (compress_hasFDerivAt R z)
  have h1 := hi.smul_const e
  have h2 := (compress_hasFDerivAt R z).const_smul ⟪e,v⟫
  have h3 := ((innerSL ℝ e).hasFDerivAt (x:=z)).smul (RadialWrapper.hessianSlice_hasFDerivAt R z v)
  convert ((h1.add h2).add h3).const_smul (a/R) using 1
  · funext q
    rw [hessianField_apply]
    simp only [Function.comp_apply,innerSL_apply,real_inner_comm v (compress R q)]
  · ext w
    simp [thirdSlice]
    module

theorem hessianField_contDiff (a R : ℝ) (hR : 0<R) (e : E) (k : ℕ) :
    ContDiff ℝ k (hessianField a R e) := by
  rw [show hessianField a R e=fderiv ℝ (gradientField a R e) from
    funext (fun z => (gradientField_hasFDerivAt a R hR e z).fderiv.symm)]
  exact (gradientField_contDiff a R e (k+1)).fderiv_right (by simp)

theorem actual_third_apply (a R : ℝ) (hR : 0<R) (e z v w : E) :
    fderiv ℝ (hessianField a R e) z w v=thirdSlice a R e z v w := by
  have hd := ((hessianField_contDiff a R hR e 1).differentiable (by norm_num) z).hasFDerivAt
  have he := hd.clm_apply (hasFDerivAt_const v z)
  have hu := (hessianField_slice_hasFDerivAt a R e z v).unique he
  have hh := congrArg (fun A : E →L[ℝ] E => A w) hu
  simpa using hh.symm

omit [CompleteSpace E] in
theorem normal_second_compression_bound (R : ℝ) (hR : 0<R) (e z v w : E) (he : ‖e‖≤1) :
    ‖⟪e,z⟫ • RadialWrapper.hessianSlice R z v w‖≤6*‖v‖*‖w‖ := by
  have hi : |⟪e,z⟫|≤‖z‖ := (abs_real_inner_le_norm e z).trans (by nlinarith [norm_nonneg z])
  have hs := scale_pos R z
  have hs1 := scale_le_one R z
  have hrad := compressed_radius_bound R hR z
  have ht : |⟪e,z⟫| * scale R z^2≤R := by
    have h1 := mul_le_mul_of_nonneg_right hi hs.le
    have h2 := mul_le_mul_of_nonneg_right hs1 (mul_nonneg (abs_nonneg ⟪e,z⟫) hs.le)
    nlinarith
  have hcoef : |⟪e,z⟫| * (6*scale R z^2/R)≤6 := by
    calc
      _ = (6*(|⟪e,z⟫| * scale R z^2))/R := by ring
      _ ≤ 6 := (div_le_iff₀ hR).mpr (by nlinarith)
  have hb := ((RadialWrapper.hessianSlice R z v).le_opNorm w).trans
    (mul_le_mul_of_nonneg_right (hessianSlice_norm_le_scale R hR z v) (norm_nonneg w))
  rw [norm_smul,Real.norm_eq_abs]
  calc
    _ ≤ |⟪e,z⟫| * ((6*scale R z^2/R)*‖v‖*‖w‖) :=
      mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = (|⟪e,z⟫| * (6*scale R z^2/R))*‖v‖*‖w‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (norm_nonneg v)) (norm_nonneg w)

omit [CompleteSpace E] in
theorem thirdSlice_apply_bound (a R : ℝ) (ha : 0≤a) (hR : 0<R)
    (e z v w : E) (he : ‖e‖≤1) :
    ‖thirdSlice a R e z v w‖≤(9*a/R)*‖v‖*‖w‖ := by
  have hdv := compressDerivative_norm_le R hR z v
  have hdw := compressDerivative_norm_le R hR z w
  have h1 : ‖⟪v,compressDerivative R z w⟫ • e‖≤‖v‖*‖w‖ := by
    rw [norm_smul,Real.norm_eq_abs]
    have hi := (abs_real_inner_le_norm v (compressDerivative R z w)).trans
      (mul_le_mul_of_nonneg_left hdw (norm_nonneg v))
    exact (mul_le_mul hi he (norm_nonneg e) (by positivity)).trans_eq (mul_one _)
  have h2 : ‖⟪e,v⟫ • compressDerivative R z w‖≤‖v‖*‖w‖ := by
    rw [norm_smul,Real.norm_eq_abs]
    have hi : |⟪e,v⟫|≤‖v‖ := (abs_real_inner_le_norm e v).trans (by nlinarith [norm_nonneg v])
    exact mul_le_mul hi hdw (norm_nonneg _) (norm_nonneg v)
  have h3 : ‖⟪e,w⟫ • compressDerivative R z v‖≤‖v‖*‖w‖ := by
    rw [norm_smul,Real.norm_eq_abs]
    have hi : |⟪e,w⟫|≤‖w‖ := (abs_real_inner_le_norm e w).trans (by nlinarith [norm_nonneg w])
    exact (mul_le_mul hi hdv (norm_nonneg _) (norm_nonneg w)).trans_eq (mul_comm _ _)
  have h4 := normal_second_compression_bound R hR e z v w he
  simp only [thirdSlice,ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.comp_apply,innerSL_apply]
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg ha hR.le)]
  calc
    _ ≤ (a/R)*(‖⟪v,compressDerivative R z w⟫ • e‖+
        ‖⟪e,v⟫ • compressDerivative R z w‖+‖⟪e,w⟫ • compressDerivative R z v‖+
        ‖⟪e,z⟫ • RadialWrapper.hessianSlice R z v w‖) :=
      mul_le_mul_of_nonneg_left
        (((norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)).trans
          (add_le_add_right (add_le_add_right (norm_add_le _ _) _) _)) (div_nonneg ha hR.le)
    _ ≤ (a/R)*(9*‖v‖*‖w‖) := mul_le_mul_of_nonneg_left (by linarith) (div_nonneg ha hR.le)
    _ = _ := by ring

theorem actual_third_norm_bound (a R : ℝ) (ha : 0≤a) (hR : 0<R)
    (e z : E) (he : ‖e‖≤1) :
    ‖fderiv ℝ (hessianField a R e) z‖≤9*a/R := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [actual_third_apply a R hR e z v w]
  convert thirdSlice_apply_bound a R ha hR e z v w he using 1
  ring

end Bilevel.PublicRadialExtension
