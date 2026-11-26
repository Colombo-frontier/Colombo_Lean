import Bilevel.PartialLegendreHybridBasic
import Bilevel.PartialLegendreJointHessian

/-! Full joint Hessian and variation of the actual hybrid scalar.
The quadratic correction and coupling contribute no Hessian variation. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.PartialLegendre
open PrimitiveGeometry
variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  {δ : NNReal} {G : Joint X Y → Joint X Y}
  (hG : LipschitzWith δ G) (hδ : δ<1) (P : Joint X Y → ℝ)
  (hP : ∀ z,HasGradientAt P (G z) z)
include hP

theorem hybridLower_regular (hquarter : (δ:ℝ)≤1/4)
    (B : Joint X Y → Joint X Y →L[ℝ] Joint X Y)
    (hDG : ∀ z,HasFDerivAt G (B z) z) {H : ℝ} (hH : 0≤H)
    (hLip : ∀ z w,‖B z-B w‖≤H*‖z-w‖) {m : ℝ} (hm : 0≤m)
    (Q : Y →L[ℝ] Y) (C : X →L[ℝ] Y)
    (hsym : ∀ u v,⟪Q u,v⟫=⟪u,Q v⟫) :
    ∃ K : Joint X Y → Joint X Y →L[ℝ] Joint X Y,
      ContDiff ℝ 2 (hybridLower hG hδ P m Q C) ∧
      (∀ z,HasFDerivAt (gradient (hybridLower hG hδ P m Q C)) (K z) z) ∧
      (∀ z,‖K z‖≤2*m+‖Q‖+‖C‖) ∧
      (∀ z w,‖K z-K w‖≤3*m*H*‖z-w‖) ∧
      (∀ z w,‖gradient (hybridLower hG hδ P m Q C) z-gradient (hybridLower hG hδ P m Q C) w‖≤
        (2*m+‖Q‖+‖C‖)*‖z-w‖) := by
  obtain ⟨K₀,hC,hD,hN,hV⟩ := jointConjugate_quarter_hessian_control hδ hG P hP hquarter B hDG hH hLip
  let K : Joint X Y → Joint X Y →L[ℝ] Joint X Y := fun z => m • K₀ z+ChiQuadratic.hessian Q C
  have hg : gradient (hybridLower hG hδ P m Q C)=
      fun z => m • gradient (jointConjugate hG hδ P) z+ChiQuadratic.hessian Q C z := by
    funext z
    rw [hybridLower_gradient hG hδ P hP m Q C hsym,jointConjugate_gradient hG hδ P hP]
  have hd (z : Joint X Y) : HasFDerivAt (gradient (hybridLower hG hδ P m Q C)) (K z) z := by
    rw [hg]
    exact ((hD z).const_smul m).add (ChiQuadratic.hessian Q C).hasFDerivAt
  have hsmul (A : Joint X Y →L[ℝ] Joint X Y) : ‖m • A‖≤m*‖A‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hm (norm_nonneg A))
    intro z
    change ‖m • A z‖≤(m*‖A‖)*‖z‖
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hm]
    exact (mul_le_mul_of_nonneg_left (A.le_opNorm z) hm).trans_eq (by ring)
  have hn (z : Joint X Y) : ‖K z‖≤2*m+‖Q‖+‖C‖ := by
    calc
      _ ≤ ‖m • K₀ z‖+‖ChiQuadratic.hessian Q C‖ := norm_add_le (m • K₀ z) (ChiQuadratic.hessian Q C)
      _ ≤ m*‖K₀ z‖+‖ChiQuadratic.hessian Q C‖ := add_le_add_right (hsmul (K₀ z)) _
      _ ≤ m*2+(‖Q‖+‖C‖) := add_le_add (mul_le_mul_of_nonneg_left (hN z).2 hm) (ChiQuadratic.hessian_norm_bound Q C)
      _ = _ := by ring
  refine ⟨K,(contDiff_const.mul hC).add (ChiQuadratic.lower_contDiff Q C 2),hd,hn,?_,?_⟩
  · intro z w
    have he : K z-K w=m • (K₀ z-K₀ w) := by dsimp [K]; module
    rw [he]
    exact (hsmul (K₀ z-K₀ w)).trans ((mul_le_mul_of_nonneg_left (hV z w) hm).trans_eq (by ring))
  · have hl : LipschitzWith ⟨2*m+‖Q‖+‖C‖,by positivity⟩ (gradient (hybridLower hG hδ P m Q C)) := by
      apply lipschitzWith_of_nnnorm_fderiv_le (fun z => (hd z).differentiableAt)
      intro z
      rw [(hd z).fderiv]
      exact_mod_cast hn z
    intro z w
    simpa only [dist_eq_norm,NNReal.coe_mk] using hl.dist_le_mul z w

end Bilevel.PartialLegendre
