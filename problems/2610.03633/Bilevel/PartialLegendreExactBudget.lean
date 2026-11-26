import Bilevel.PartialLegendreQuadraticNorm

/-! The actual lower primitive meets the prescribed full-gradient budget L.
Quadratic block slack absorbs the Legendre perturbation without a factor
depending on the number or dimension of blocks. -/
noncomputable section
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 1200000
namespace Bilevel.PartialLegendre
open PrimitiveGeometry

variable {X U V : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem normalHessian_perturbation_bound {m C : ℝ} (hm : 0≤m) (c : ℝ)
    (K : Joint X (Joint U V) → Joint X (Joint U V) →L[ℝ] Joint X (Joint U V))
    (hK : ∀ z,‖K z-lowerProjection‖≤C) (q : FullNormalVariables X U V) :
    ‖conjugateCouplingHessian normalConjugateProjection normalOuterProjection normalTangentProjection m c K q-
      normalQuadraticOperator m c‖≤m*C := by
  let T : FullNormalVariables X U V →L[ℝ] Joint X (Joint U V) := normalConjugateProjection
  let A : FullNormalVariables X U V →L[ℝ] U := normalOuterProjection
  let B : FullNormalVariables X U V →L[ℝ] U := normalTangentProjection
  have hT : ‖T‖≤1 := normalConjugateProjection_norm
  have hC : 0≤C := (norm_nonneg (K (T q)-lowerProjection)).trans (hK _)
  have he : conjugateCouplingHessian T A B m c K q-normalQuadraticOperator m c=
      m • T.adjoint.comp ((K (T q)-lowerProjection).comp T) := by
    ext v
    simp only [conjugateCouplingHessian,normalQuadraticOperator,ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,map_sub,smul_sub]
    change (m • T.adjoint (K (T q) (T v))-c • bilinearCouplingOperator A B v)-
      (m • T.adjoint (lowerProjection (T v))-c • bilinearCouplingOperator A B v)= _
    abel
  change ‖conjugateCouplingHessian T A B m c K q-normalQuadraticOperator m c‖≤m*C
  rw [he]
  let D : FullNormalVariables X U V →L[ℝ] FullNormalVariables X U V :=
    T.adjoint.comp ((K (T q)-lowerProjection).comp T)
  change ‖m • D‖≤m*C
  have hD : ‖D‖≤C := by
    calc
      _ ≤ ‖T.adjoint‖*(‖K (T q)-lowerProjection‖*‖T‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1*(C*1) := by rw [ContinuousLinearMap.adjoint.norm_map];gcongr;exact hK _
      _ = C := by ring
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hm hC)
  intro v
  change ‖m • D v‖≤m*C*‖v‖
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hm]
  calc
    _ ≤ m*(C*‖v‖) := mul_le_mul_of_nonneg_left
      ((D.le_opNorm v).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg v))) hm
    _ = m*C*‖v‖ := by ring

variable {δ : NNReal} {G : Joint X (Joint U V) → Joint X (Joint U V)}
  (hG : LipschitzWith δ G) (hδ : δ<1) (P : Joint X (Joint U V) → ℝ)

theorem fullJointNormalLower_exact_budget (hsmall : (δ:ℝ)≤1/12)
    (hP : ∀ q,HasGradientAt P (G q) q)
    (B : Joint X (Joint U V) → Joint X (Joint U V) →L[ℝ] Joint X (Joint U V))
    (hDG : ∀ z,HasFDerivAt G (B z) z) {H μ L : ℝ} (hH : 0≤H)
    (hLip : ∀ z w,‖B z-B w‖≤H*‖z-w‖) (hμ : 0<μ) (hμL : 2*μ≤L) :
    ∃ K : FullNormalVariables X U V → FullNormalVariables X U V →L[ℝ] FullNormalVariables X U V,
      ContDiff ℝ 2 (fullJointNormalLower hG hδ P (3*μ/2) (L/4)) ∧
      (∀ q,HasFDerivAt (gradient (fullJointNormalLower hG hδ P (3*μ/2) (L/4))) (K q) q) ∧
      (∀ q,‖K q‖≤L) ∧
      (∀ q r,‖K q-K r‖≤(9*μ*H/2)*‖q-r‖) ∧
      (∀ q r,‖gradient (fullJointNormalLower hG hδ P (3*μ/2) (L/4)) q-
        gradient (fullJointNormalLower hG hδ P (3*μ/2) (L/4)) r‖≤L*‖q-r‖) := by
  have hL : 0≤L := by linarith
  have hm : 0≤3*μ/2 := by positivity
  obtain ⟨K,hC,hD,hN,hV⟩ := jointConjugate_quarter_hessian_control hδ hG P hP (by linarith) B hDG hH hLip
  let T : FullNormalVariables X U V →L[ℝ] Joint X (Joint U V) := normalConjugateProjection
  let A : FullNormalVariables X U V →L[ℝ] U := normalOuterProjection
  let B' : FullNormalVariables X U V →L[ℝ] U := normalTangentProjection
  have hT : ‖T‖≤1 := normalConjugateProjection_norm
  let Kfull := conjugateCouplingHessian T A B' (3*μ/2) (L/4) K
  have hquad : ‖(normalQuadraticOperator (3*μ/2) (L/4) : FullNormalVariables X U V →L[ℝ] FullNormalVariables X U V)‖≤7*L/8 :=
    normalQuadraticOperator_norm_bound hm hL (by linarith)
  have hpert : (3*μ/2)*(2*(δ:ℝ))≤L/8 := by
    have hh := mul_le_mul_of_nonneg_left hsmall (show 0≤3*μ by positivity)
    nlinarith
  have hn (q : FullNormalVariables X U V) : ‖Kfull q‖≤L := by
    let Q : FullNormalVariables X U V →L[ℝ] FullNormalVariables X U V :=
      normalQuadraticOperator (3*μ/2) (L/4)
    have hQ : ‖Q‖≤7*L/8 := hquad
    have hp := normalHessian_perturbation_bound hm (L/4) K (fun z => (hN z).1) q
    change ‖Kfull q-Q‖≤_ at hp
    have hh : ‖Kfull q‖≤‖Kfull q-Q‖+‖Q‖ := by
      simpa only [sub_add_cancel] using norm_add_le (Kfull q-Q) Q
    linarith
  rw [fullJointNormalLower_eq]
  have hd := conjugateCoupling_gradient_hasFDerivAt hG hδ P hP T A B' (3*μ/2) (L/4) K hD
  refine ⟨Kfull,conjugateCoupling_contDiff_two hG hδ P T A B' (3*μ/2) (L/4) hC,hd,hn,?_,?_⟩
  · intro q r
    have hh := conjugateCouplingHessian_variation T A B' hT hm (L/4) K
      (show 0≤3*H by positivity) hV q r
    convert hh using 1
    ring
  · have hl : LipschitzWith ⟨L,hL⟩
        (gradient (conjugateCoupling hG hδ P T A B' (3*μ/2) (L/4))) := by
      apply lipschitzWith_of_nnnorm_fderiv_le (fun q => (hd q).differentiableAt)
      intro q
      rw [(hd q).fderiv]
      exact_mod_cast hn q
    intro q r
    simpa only [dist_eq_norm,NNReal.coe_mk] using hl.dist_le_mul q r

end Bilevel.PartialLegendre
