import Bilevel.PartialLegendreJointCoupling

/-! Source lower objective with the complete variable (x,v,u,r).
Its full gradient and Hessian are those of the actual partial conjugate. -/
noncomputable section
namespace Bilevel.PartialLegendre
open PrimitiveGeometry

variable {X U V : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

def jointFstLinear {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] : Joint A B →L[ℝ] A :=
  (ContinuousLinearMap.fst ℝ A B).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ A B).toContinuousLinearMap

def jointSndLinear {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] : Joint A B →L[ℝ] B :=
  (ContinuousLinearMap.snd ℝ A B).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ A B).toContinuousLinearMap

abbrev FullNormalVariables (X U V : Type*) := Joint (Joint X U) (Joint U V)

def normalConjugateProjection : FullNormalVariables X U V →L[ℝ] Joint X (Joint U V) :=
  packLinear.comp ((jointFstLinear.comp jointFstLinear).prod jointSndLinear)

def normalOuterProjection : FullNormalVariables X U V →L[ℝ] U :=
  jointSndLinear.comp jointFstLinear

def normalTangentProjection : FullNormalVariables X U V →L[ℝ] U :=
  jointFstLinear.comp jointSndLinear

omit [CompleteSpace X] [CompleteSpace U] [CompleteSpace V] in
theorem normalConjugateProjection_apply (q : FullNormalVariables X U V) :
    normalConjugateProjection q=pack q.fst.fst q.snd := rfl

omit [CompleteSpace X] [CompleteSpace U] [CompleteSpace V] in
theorem normalConjugateProjection_norm :
    ‖(normalConjugateProjection : FullNormalVariables X U V →L[ℝ] Joint X (Joint U V))‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro q
  rw [one_mul,normalConjugateProjection_apply]
  have ha := norm_sq q
  have hb := norm_sq q.fst
  have hc := norm_sq (pack q.fst.fst q.snd)
  change ‖pack q.fst.fst q.snd‖^2=‖q.fst.fst‖^2+‖q.snd‖^2 at hc
  nlinarith [norm_nonneg q,norm_nonneg (pack q.fst.fst q.snd),sq_nonneg ‖q.fst.snd‖]

omit [CompleteSpace X] [CompleteSpace U] [CompleteSpace V] in
theorem normalOuterProjection_norm :
    ‖(normalOuterProjection : FullNormalVariables X U V →L[ℝ] U)‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro q
  change ‖q.fst.snd‖≤1*‖q‖
  rw [one_mul]
  exact (WithLp.norm_snd_le X q.fst).trans (WithLp.norm_fst_le (Joint X U) q)

omit [CompleteSpace X] [CompleteSpace U] [CompleteSpace V] in
theorem normalTangentProjection_norm :
    ‖(normalTangentProjection : FullNormalVariables X U V →L[ℝ] U)‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro q
  change ‖q.snd.fst‖≤1*‖q‖
  rw [one_mul]
  exact (WithLp.norm_fst_le U q.snd).trans (WithLp.norm_snd_le (Joint X U) q)

variable {δ : NNReal} {G : Joint X (Joint U V) → Joint X (Joint U V)}
  (hG : LipschitzWith δ G) (hδ : δ<1) (P : Joint X (Joint U V) → ℝ)

def fullJointNormalLower (m c : ℝ) (q : FullNormalVariables X U V) : ℝ :=
  jointNormalLower hG hδ P m c q.fst.fst q.fst.snd q.snd

omit [CompleteSpace X] in
theorem fullJointNormalLower_eq (m c : ℝ) :
    fullJointNormalLower hG hδ P m c=
      conjugateCoupling hG hδ P normalConjugateProjection
        normalOuterProjection normalTangentProjection m c := rfl

/-- Dimension-free full joint regularity, retaining the outer coupling variable.
The Hessian is an actual derivative, and the gradient bound follows from it. -/
theorem fullJointNormalLower_regular (hquarter : (δ:ℝ)≤1/4)
    (hP : ∀ q,HasGradientAt P (G q) q)
    (B : Joint X (Joint U V) → Joint X (Joint U V) →L[ℝ] Joint X (Joint U V))
    (hDG : ∀ z,HasFDerivAt G (B z) z) {H : ℝ} (hH : 0≤H)
    (hLip : ∀ z w,‖B z-B w‖≤H*‖z-w‖) {m : ℝ} (hm : 0≤m) (c : ℝ) :
    ∃ K : FullNormalVariables X U V → FullNormalVariables X U V →L[ℝ] FullNormalVariables X U V,
      ContDiff ℝ 2 (fullJointNormalLower hG hδ P m c) ∧
      (∀ q,HasFDerivAt (gradient (fullJointNormalLower hG hδ P m c)) (K q) q) ∧
      (∀ q,‖K q‖≤2*m+2*|c|) ∧
      (∀ q r,‖K q-K r‖≤3*m*H*‖q-r‖) ∧
      (∀ q r,‖gradient (fullJointNormalLower hG hδ P m c) q-
        gradient (fullJointNormalLower hG hδ P m c) r‖≤(2*m+2*|c|)*‖q-r‖) := by
  obtain ⟨K,hC,hD,hN,hV⟩ :=
    jointConjugate_quarter_hessian_control hδ hG P hP hquarter B hDG hH hLip
  rw [fullJointNormalLower_eq]
  let T : FullNormalVariables X U V →L[ℝ] Joint X (Joint U V) := normalConjugateProjection
  let A : FullNormalVariables X U V →L[ℝ] U := normalOuterProjection
  let B' : FullNormalVariables X U V →L[ℝ] U := normalTangentProjection
  have hT : ‖T‖≤1 := normalConjugateProjection_norm
  have hA : ‖A‖≤1 := normalOuterProjection_norm
  have hB' : ‖B'‖≤1 := normalTangentProjection_norm
  have hd := conjugateCoupling_gradient_hasFDerivAt hG hδ P hP T A B' m c K hD
  have hn : ∀ q,‖conjugateCouplingHessian T A B' m c K q‖≤2*m+2*|c| := by
    intro q
    simpa only [mul_comm m 2] using
      conjugateCouplingHessian_norm T A B' hT hA hB' hm c K (fun z => (hN z).2) q
  refine ⟨conjugateCouplingHessian T A B' m c K,
    conjugateCoupling_contDiff_two hG hδ P T A B' m c hC,hd,hn,?_,?_⟩
  · intro q r
    have hh := conjugateCouplingHessian_variation T A B' hT hm c K
      (show 0≤3*H by positivity) hV q r
    convert hh using 1
    ring
  · have hl : LipschitzWith ⟨2*m+2*|c|,by positivity⟩
        (gradient (conjugateCoupling hG hδ P T A B' m c)) := by
      apply lipschitzWith_of_nnnorm_fderiv_le (fun q => (hd q).differentiableAt)
      intro q
      rw [(hd q).fderiv]
      exact_mod_cast hn q
    intro q r
    simpa only [dist_eq_norm,NNReal.coe_mk] using hl.dist_le_mul q r

end Bilevel.PartialLegendre
