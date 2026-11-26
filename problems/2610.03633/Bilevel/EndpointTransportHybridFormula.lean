import Bilevel.EndpointTransportHybridPrimitive

/-! The constructed correction is exactly the physical-block quadratic in
the manuscript. Ordinary and normal coordinates receive no correction. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre
variable {E U V : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem hybrid_correction_apply {n D : ℕ} (m δ : ℝ) (Q : Rotations n D) (y : HybridVariables U V n D) :
    ChiHybrid.correction (hybridHessian m δ Q) m y=
      pack (pack (0:U) (physicalHessian δ Q y.fst.snd-m • y.fst.snd)) (0:V) := by
  rw [ChiHybrid.correction_apply,hybridHessian_apply]
  change pack (pack (m • y.fst.fst-m • y.fst.fst)
    (physicalHessian δ Q y.fst.snd-m • y.fst.snd)) (m • y.snd-m • y.snd)=_
  simp only [sub_self]

theorem hybrid_correction_inner {n D : ℕ} (m δ : ℝ) (Q : Rotations n D) (y : HybridVariables U V n D) :
    ⟪y,ChiHybrid.correction (hybridHessian m δ Q) m y⟫=
      ⟪y.fst.snd,physicalHessian δ Q y.fst.snd⟫-m*‖y.fst.snd‖^2 := by
  rw [hybrid_correction_apply]
  change (⟪y.fst.fst,(0:U)⟫+⟪y.fst.snd,physicalHessian δ Q y.fst.snd-m • y.fst.snd⟫)+⟪y.snd,(0:V)⟫=_
  simp only [inner_zero_right,zero_add,add_zero,inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq]

theorem hybrid_coupling_inner {n D : ℕ} (c₀ cend : ℝ) (Q : Rotations n D)
    (x : HybridOuter E U D) (y : HybridVariables U V n D) :
    ⟪hybridCoupling c₀ cend Q x,y⟫=c₀*⟪x.fst.snd,y.fst.fst⟫+
      cend*⟪Q (Fin.last (n+1)) x.snd,y.fst.snd (Fin.last (n+1))⟫ := by
  rw [hybridCoupling_apply]
  change (⟪c₀ • x.fst.snd,y.fst.fst⟫+⟪endpointCoupling cend Q x,y.fst.snd⟫)+⟪(0:V),y.snd⟫=_
  rw [inner_zero_left,add_zero,real_inner_smul_left,endpointCoupling_inner]

variable [CompleteSpace E] [CompleteSpace U] [CompleteSpace V]

theorem sourceHybridLower_formula {D : ℕ} (L κ : ℝ)
    (Q : Rotations (EndpointTransportNormalization.interiors κ) D)
    (P : Joint (HybridOuter E U D) (HybridVariables U V (EndpointTransportNormalization.interiors κ) D) → ℝ)
    (hP : ContDiff ℝ 3 P) (δ : NNReal) (h2 : ∀ z,‖iteratedFDeriv ℝ 2 P z‖≤(δ:ℝ)) (hδ : δ<1)
    (x : HybridOuter E U D) (y : HybridVariables U V (EndpointTransportNormalization.interiors κ) D) :
    sourceHybridLower L κ Q P hP δ h2 hδ (pack x y)=
      (3*(L/κ)/2)*jointConjugate (ChiHybrid.extensionGradientLipschitz P hP δ h2) hδ P (pack x y)+
      (1/2)*(⟪y.fst.snd,physicalHessian (L/16) Q y.fst.snd⟫-(3*(L/κ)/2)*‖y.fst.snd‖^2)-
      EndpointTransportNormalization.coupling L κ*⟪x.fst.snd,y.fst.fst⟫-
      (L/4)*⟪Q (Fin.last (EndpointTransportNormalization.interiors κ+1)) x.snd,
        y.fst.snd (Fin.last (EndpointTransportNormalization.interiors κ+1))⟫ := by
  unfold sourceHybridLower ChiHybrid.lowerOfExtension hybridLower ChiQuadratic.lower
  change (3*(L/κ)/2)*jointConjugate _ hδ P (pack x y)+
    ((1/2)*⟪y,ChiHybrid.correction (hybridHessian (3*(L/κ)/2) (L/16) Q) (3*(L/κ)/2) y⟫-
      ⟪hybridCoupling (EndpointTransportNormalization.coupling L κ) (L/4) Q x,y⟫)=_
  rw [hybrid_correction_inner,hybrid_coupling_inner]
  ring

end Bilevel.EndpointTransportResponse
