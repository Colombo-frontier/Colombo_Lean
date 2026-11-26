import Bilevel.PartialLegendreJointInverse
import Bilevel.PartialLegendreVariation

/-! Actual full joint Hessian bounds and variation of the partial conjugate.
The operator identity H_L=Q_y-DG(S) (I+Q_y DG(S))^-1 includes every mixed
macro/lower derivative, and gives the source C^{2,1} estimates. -/
noncomputable section
namespace Bilevel.PartialLegendre
open PrimitiveGeometry

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  {δ : NNReal} (hδ : δ<1)

theorem jointHessian_sub_projection_norm (B : Joint X Y →L[ℝ] Joint X Y)
    (hB : ‖B‖≤(δ:ℝ)) :
    ‖jointHessian hδ B hB-lowerProjection‖≤(δ:ℝ)/(1-(δ:ℝ)) := by
  have hd : 0<1-(δ:ℝ) := sub_pos.mpr (show (δ:ℝ)<1 from hδ)
  have he : jointHessian hδ B hB-lowerProjection = -(B.comp (jointInverseDerivative hδ B hB)) := by
    unfold jointHessian
    abel
  rw [he,_root_.norm_neg (B.comp (jointInverseDerivative hδ B hB))]
  calc
    _ ≤ ‖B‖*‖jointInverseDerivative hδ B hB‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (δ:ℝ)*(1/(1-(δ:ℝ))) :=
      mul_le_mul hB (jointInverseDerivative_norm hδ B hB)
        (norm_nonneg (jointInverseDerivative hδ B hB)) δ.coe_nonneg
    _ = _ := by ring

theorem jointHessian_norm (B : Joint X Y →L[ℝ] Joint X Y) (hB : ‖B‖≤(δ:ℝ)) :
    ‖jointHessian hδ B hB‖≤1/(1-(δ:ℝ)) := by
  have hd : 0<1-(δ:ℝ) := sub_pos.mpr (show (δ:ℝ)<1 from hδ)
  have hh := norm_sub_le_norm_sub_add_norm_sub (jointHessian hδ B hB) lowerProjection 0
  rw [sub_zero,sub_zero] at hh
  have hb := jointHessian_sub_projection_norm hδ B hB
  have hp := lowerProjection_norm (X := X) (Y := Y)
  have he : (δ:ℝ)/(1-(δ:ℝ))+1=1/(1-(δ:ℝ)) := by field_simp
  linarith

theorem jointInverseDerivative_difference_bound (B C : Joint X Y →L[ℝ] Joint X Y)
    (hB : ‖B‖≤(δ:ℝ)) (hC : ‖C‖≤(δ:ℝ)) :
    ‖jointInverseDerivative hδ B hB-jointInverseDerivative hδ C hC‖≤
      (1-(δ:ℝ))⁻¹^2*‖B-C‖ := by
  have hh := linearEquiv_inverse_difference_bound hδ (lowerProjection.comp B) (lowerProjection.comp C)
    ((lowerProjection_comp_norm B).trans hB) ((lowerProjection_comp_norm C).trans hC)
  have he : lowerProjection.comp B-lowerProjection.comp C=lowerProjection.comp (B-C) := by
    ext v
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,map_sub]
  rw [he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (lowerProjection_comp_norm (B-C)) (sq_nonneg _))

theorem jointHessian_difference_bound (B C : Joint X Y →L[ℝ] Joint X Y)
    (hB : ‖B‖≤(δ:ℝ)) (hC : ‖C‖≤(δ:ℝ)) :
    ‖jointHessian hδ B hB-jointHessian hδ C hC‖≤(1-(δ:ℝ))⁻¹^2*‖B-C‖ := by
  have hd : 0<1-(δ:ℝ) := sub_pos.mpr (show (δ:ℝ)<1 from hδ)
  have hδ0 : 0≤(δ:ℝ) := δ.coe_nonneg
  have he : jointHessian hδ B hB-jointHessian hδ C hC =
      -(B.comp (jointInverseDerivative hδ B hB)-C.comp (jointInverseDerivative hδ C hC)) := by
    unfold jointHessian
    abel
  have hid : B.comp (jointInverseDerivative hδ B hB)-C.comp (jointInverseDerivative hδ C hC) =
      (B-C).comp (jointInverseDerivative hδ B hB)+
        C.comp (jointInverseDerivative hδ B hB-jointInverseDerivative hδ C hC) := by
    ext v
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,map_sub]
    abel
  rw [he,_root_.norm_neg (B.comp (jointInverseDerivative hδ B hB)-C.comp (jointInverseDerivative hδ C hC)),hid]
  calc
    _ ≤ ‖(B-C).comp (jointInverseDerivative hδ B hB)‖+
        ‖C.comp (jointInverseDerivative hδ B hB-jointInverseDerivative hδ C hC)‖ :=
      norm_add_le ((B-C).comp (jointInverseDerivative hδ B hB))
        (C.comp (jointInverseDerivative hδ B hB-jointInverseDerivative hδ C hC))
    _ ≤ ‖B-C‖*‖jointInverseDerivative hδ B hB‖+
        ‖C‖*‖jointInverseDerivative hδ B hB-jointInverseDerivative hδ C hC‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ ‖B-C‖*(1/(1-(δ:ℝ)))+(δ:ℝ)*((1-(δ:ℝ))⁻¹^2*‖B-C‖) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (jointInverseDerivative_norm hδ B hB) (norm_nonneg (B-C))
      · exact mul_le_mul hC (jointInverseDerivative_difference_bound hδ B C hB hC)
          (norm_nonneg (jointInverseDerivative hδ B hB-jointInverseDerivative hδ C hC)) hδ0
    _ = _ := by field_simp [hd.ne']; ring

variable {G : Joint X Y → Joint X Y} (hG : LipschitzWith δ G)

omit [CompleteSpace X] [CompleteSpace Y] in
include hG in
theorem jointDerivative_norm (z : Joint X Y) (B : Joint X Y →L[ℝ] Joint X Y)
    (hDG : HasFDerivAt G B z) : ‖B‖≤(δ:ℝ) :=
  hDG.le_of_lip' δ.coe_nonneg (Filter.Eventually.of_forall
    (fun w => by simpa only [dist_eq_norm] using hG.dist_le_mul w z))

def jointHessianField (B : Joint X Y → Joint X Y →L[ℝ] Joint X Y)
    (hB : ∀ z,‖B z‖≤(δ:ℝ)) (q : Joint X Y) : Joint X Y →L[ℝ] Joint X Y :=
  jointHessian hδ (B (jointInverse hG hδ q)) (hB _)

theorem jointHessianField_variation (B : Joint X Y → Joint X Y →L[ℝ] Joint X Y)
    (hB : ∀ z,‖B z‖≤(δ:ℝ)) {H : ℝ} (hH : 0≤H)
    (hLip : ∀ z w,‖B z-B w‖≤H*‖z-w‖) (q r : Joint X Y) :
    ‖jointHessianField hδ hG B hB q-jointHessianField hδ hG B hB r‖≤
      H/(1-(δ:ℝ))^3*‖q-r‖ := by
  have hd : 0<1-(δ:ℝ) := sub_pos.mpr (show (δ:ℝ)<1 from hδ)
  calc
    _ ≤ (1-(δ:ℝ))⁻¹^2*‖B (jointInverse hG hδ q)-B (jointInverse hG hδ r)‖ :=
      jointHessian_difference_bound hδ _ _ _ _
    _ ≤ (1-(δ:ℝ))⁻¹^2*(H*(‖q-r‖/(1-(δ:ℝ)))) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact (hLip _ _).trans (mul_le_mul_of_nonneg_left (jointInverse_lipschitz_bound hG hδ q r) hH)
    _ = _ := by simp only [div_eq_mul_inv,← inv_pow]; ring

theorem jointHessianField_continuous (B : Joint X Y → Joint X Y →L[ℝ] Joint X Y)
    (hB : ∀ z,‖B z‖≤(δ:ℝ)) {H : ℝ} (hH : 0≤H)
    (hLip : ∀ z w,‖B z-B w‖≤H*‖z-w‖) : Continuous (jointHessianField hδ hG B hB) := by
  have hd : 0<1-(δ:ℝ) := sub_pos.mpr (show (δ:ℝ)<1 from hδ)
  have hl : LipschitzWith ⟨H/(1-(δ:ℝ))^3,by positivity⟩ (jointHessianField hδ hG B hB) := by
    apply LipschitzWith.of_dist_le_mul
    intro q r
    simpa only [dist_eq_norm,NNReal.coe_mk] using jointHessianField_variation hδ hG B hB hH hLip q r
  exact hl.continuous

variable (P : Joint X Y → ℝ) (hP : ∀ q,HasGradientAt P (G q) q)
include hP

theorem jointConjugate_gradient_contDiff_one (B : Joint X Y → Joint X Y →L[ℝ] Joint X Y)
    (hB : ∀ z,‖B z‖≤(δ:ℝ)) (hDG : ∀ z,HasFDerivAt G (B z) z)
    {H : ℝ} (hH : 0≤H) (hLip : ∀ z w,‖B z-B w‖≤H*‖z-w‖) :
    ContDiff ℝ 1 (gradient (jointConjugate hG hδ P)) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  exact ⟨jointHessianField hδ hG B hB,jointHessianField_continuous hδ hG B hB hH hLip,
    fun q => jointConjugate_gradient_hasFDerivAt hG hδ P hP q _ (hB _) (hDG _)⟩

theorem jointConjugate_contDiff_two (B : Joint X Y → Joint X Y →L[ℝ] Joint X Y)
    (hB : ∀ z,‖B z‖≤(δ:ℝ)) (hDG : ∀ z,HasFDerivAt G (B z) z)
    {H : ℝ} (hH : 0≤H) (hLip : ∀ z w,‖B z-B w‖≤H*‖z-w‖) :
    ContDiff ℝ 2 (jointConjugate hG hδ P) := by
  apply contDiff_succ_iff_hasFDerivAt.mpr
  refine ⟨fun q => InnerProductSpace.toDual ℝ (Joint X Y) (gradient (jointConjugate hG hδ P) q),?_,?_⟩
  · exact (InnerProductSpace.toDual ℝ (Joint X Y)).contDiff.comp
      (jointConjugate_gradient_contDiff_one hδ hG P hP B hB hDG hH hLip)
  · intro q
    dsimp only
    rw [jointConjugate_gradient hG hδ P hP q]
    exact (jointConjugate_hasGradientAt hG hδ P hP q).hasFDerivAt

/-- Actual C2 function and actual Lipschitz Hessian, with the original
derivative norm budget derived from the given full-gradient Lipschitz bound. -/
theorem jointConjugate_hessian_control (B : Joint X Y → Joint X Y →L[ℝ] Joint X Y)
    (hDG : ∀ z,HasFDerivAt G (B z) z) {H : ℝ} (hH : 0≤H)
    (hLip : ∀ z w,‖B z-B w‖≤H*‖z-w‖) :
    ∃ K : Joint X Y → Joint X Y →L[ℝ] Joint X Y,
      ContDiff ℝ 2 (jointConjugate hG hδ P) ∧
      (∀ q,HasFDerivAt (gradient (jointConjugate hG hδ P)) (K q) q) ∧
      (∀ q,‖K q-lowerProjection‖≤(δ:ℝ)/(1-(δ:ℝ)) ∧ ‖K q‖≤1/(1-(δ:ℝ))) ∧
      (∀ q r,‖K q-K r‖≤H/(1-(δ:ℝ))^3*‖q-r‖) := by
  let hB : ∀ z,‖B z‖≤(δ:ℝ) := fun z => jointDerivative_norm hG z (B z) (hDG z)
  refine ⟨jointHessianField hδ hG B hB,jointConjugate_contDiff_two hδ hG P hP B hB hDG hH hLip,?_,?_,?_⟩
  · intro q
    exact jointConjugate_gradient_hasFDerivAt hG hδ P hP q _ (hB _) (hDG _)
  · intro q
    exact ⟨jointHessian_sub_projection_norm hδ _ (hB _),jointHessian_norm hδ _ (hB _)⟩
  · exact jointHessianField_variation hδ hG B hB hH hLip

/-- Explicit dimension-free constants in the source regime delta≤1/4. -/
theorem jointConjugate_quarter_hessian_control (hquarter : (δ:ℝ)≤1/4)
    (B : Joint X Y → Joint X Y →L[ℝ] Joint X Y)
    (hDG : ∀ z,HasFDerivAt G (B z) z) {H : ℝ} (hH : 0≤H)
    (hLip : ∀ z w,‖B z-B w‖≤H*‖z-w‖) :
    ∃ K : Joint X Y → Joint X Y →L[ℝ] Joint X Y,
      ContDiff ℝ 2 (jointConjugate hG hδ P) ∧
      (∀ q,HasFDerivAt (gradient (jointConjugate hG hδ P)) (K q) q) ∧
      (∀ q,‖K q-lowerProjection‖≤2*(δ:ℝ) ∧ ‖K q‖≤2) ∧
      (∀ q r,‖K q-K r‖≤3*H*‖q-r‖) := by
  obtain ⟨K,hC,hD,hN,hV⟩ := jointConjugate_hessian_control hδ hG P hP B hDG hH hLip
  have hd : 0<1-(δ:ℝ) := sub_pos.mpr (show (δ:ℝ)<1 from hδ)
  have hi : 1/(1-(δ:ℝ))≤4/3 := (div_le_iff₀ hd).mpr (by linarith)
  have hi0 : 0≤1/(1-(δ:ℝ)) := by positivity
  have hic : (1/(1-(δ:ℝ)))^3≤(4/3:ℝ)^3 := by gcongr
  have hi3 : (1/(1-(δ:ℝ)))^3≤3 := hic.trans (by norm_num)
  have hclose : (δ:ℝ)/(1-(δ:ℝ))≤2*(δ:ℝ) := by
    calc
      _ = (δ:ℝ)*(1/(1-(δ:ℝ))) := by ring
      _ ≤ (δ:ℝ)*(4/3) := mul_le_mul_of_nonneg_left hi δ.coe_nonneg
      _ ≤ _ := by have hh := δ.coe_nonneg; linarith
  have hvar : H/(1-(δ:ℝ))^3≤3*H := by
    calc
      _ = H*(1/(1-(δ:ℝ)))^3 := by simp only [one_div,div_eq_mul_inv,← inv_pow,one_mul]
      _ ≤ H*3 := mul_le_mul_of_nonneg_left hi3 hH
      _ = _ := by ring
  refine ⟨K,hC,hD,fun q => ⟨(hN q).1.trans hclose,(hN q).2.trans (by linarith)⟩,?_⟩
  intro q r
  exact (hV q r).trans (mul_le_mul_of_nonneg_right hvar (norm_nonneg _))

end Bilevel.PartialLegendre
