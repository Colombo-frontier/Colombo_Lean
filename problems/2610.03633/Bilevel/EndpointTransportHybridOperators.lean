import Bilevel.EndpointTransportHybridBlocks

/-! Actual heterogeneous physical tangent, normal block, and endpoint
coupling of the transport hybrid construction. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre
variable {E U V : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

abbrev HybridOuter (E U : Type*) (D : ℕ) := Joint (Joint E U) (Block D)
abbrev HybridTangent (U : Type*) (n D : ℕ) := Joint U (Physical n D)
abbrev HybridVariables (U V : Type*) (n D : ℕ) := Joint (HybridTangent U n D) V

def hybridHessian {n D : ℕ} (m δ : ℝ) (Q : Rotations n D) :
    HybridVariables U V n D →L[ℝ] HybridVariables U V n D :=
  jointOperator (jointOperator (m • ContinuousLinearMap.id ℝ U) (physicalHessian δ Q))
    (m • ContinuousLinearMap.id ℝ V)

def hybridCoupling {n D : ℕ} (c₀ cend : ℝ) (Q : Rotations n D) :
    HybridOuter E U D →L[ℝ] HybridVariables U V n D :=
  packLinear.comp ((packLinear.comp
    ((c₀ • (jointSndLinear.comp jointFstLinear)).prod (endpointCoupling cend Q))).prod 0)

def hybridTangentResponse {n D : ℕ} (δ cend K : ℝ) (Q : Rotations n D) (x : HybridOuter E U D) :
    HybridTangent U n D := pack (K • x.fst.snd) (physicalResponse δ cend Q x.snd)

theorem hybridHessian_apply {n D : ℕ} (m δ : ℝ) (Q : Rotations n D) (y : HybridVariables U V n D) :
    hybridHessian m δ Q y=pack (pack (m • y.fst.fst) (physicalHessian δ Q y.fst.snd)) (m • y.snd) := rfl

theorem hybridCoupling_apply {n D : ℕ} (c₀ cend : ℝ) (Q : Rotations n D) (x : HybridOuter E U D) :
    hybridCoupling (V:=V) c₀ cend Q x=pack (pack (c₀ • x.fst.snd) (endpointCoupling cend Q x)) 0 := rfl

theorem hybridHessian_symmetric {n D : ℕ} (m δ : ℝ) (Q : Rotations n D)
    (y z : HybridVariables U V n D) : ⟪hybridHessian m δ Q y,z⟫=⟪y,hybridHessian m δ Q z⟫ := by
  apply jointOperator_symmetric
  · intro a b
    apply jointOperator_symmetric
    · intro u v
      simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,real_inner_smul_left,real_inner_smul_right]
    · exact physicalHessian_symmetric δ Q
  · intro u v
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,real_inner_smul_left,real_inner_smul_right]

theorem hybridHessian_coercive {n D : ℕ} (m δ : ℝ) (Q : Rotations n D)
    (hphysical : ∀ Y : Physical n D,m*‖Y‖^2≤⟪Y,physicalHessian δ Q Y⟫)
    (y : HybridVariables U V n D) : m*‖y‖^2≤⟪y,hybridHessian m δ Q y⟫ := by
  apply jointOperator_coercive
  · intro u
    apply jointOperator_coercive
    · intro v
      simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,real_inner_smul_right,real_inner_self_eq_norm_sq,le_refl]
    · exact hphysical
  · intro v
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,real_inner_smul_right,real_inner_self_eq_norm_sq,le_refl]

theorem hybridHessian_norm_bound {n D : ℕ} {m δ K : ℝ} (hm : 0≤m) (hmK : m≤K)
    (Q : Rotations n D) (hphysical : ‖physicalHessian δ Q‖≤K) :
    ‖(hybridHessian (U:=U) (V:=V) m δ Q)‖≤K := by
  have hK : 0≤K := hm.trans hmK
  have hU : ‖m • ContinuousLinearMap.id ℝ U‖≤K := by
    exact (scalarIdentity_norm m).trans (by rwa [abs_of_nonneg hm])
  have hV : ‖m • ContinuousLinearMap.id ℝ V‖≤K := by
    exact (scalarIdentity_norm m).trans (by rwa [abs_of_nonneg hm])
  exact jointOperator_norm_bound _ _ hK (jointOperator_norm_bound _ _ hK hU hphysical) hV

theorem hybridHessian_on_normal {n D : ℕ} (m δ : ℝ) (Q : Rotations n D) (v : V) :
    hybridHessian (U:=U) m δ Q (pack (0:HybridTangent U n D) v)=m • pack (0:HybridTangent U n D) v := by
  rw [hybridHessian_apply]
  change pack (pack (m • (0:U)) (physicalHessian δ Q 0)) (m • v)=pack (m • (0:HybridTangent U n D)) (m • v)
  simp only [smul_zero,map_zero]
  rfl

theorem hybrid_response_equation {n D : ℕ} {δ m c₀ cend K : ℝ} (hδ : δ≠0)
    (hK : m*K=c₀) (Q : Rotations n D) (x : HybridOuter E U D) :
    hybridHessian m δ Q (pack (hybridTangentResponse δ cend K Q x) (0:V))=hybridCoupling c₀ cend Q x := by
  rw [hybridHessian_apply,hybridCoupling_apply]
  change pack (pack (m • (K • x.fst.snd)) (physicalHessian δ Q (physicalResponse δ cend Q x.snd))) (m • (0:V))=_
  rw [smul_smul,hK,smul_zero,physical_response_equation hδ cend Q x]

theorem hybridCoupling_norm_bound {n D : ℕ} {c₀ cend K : ℝ} (Q : Rotations n D)
    (hK : 0≤K) (h₀ : |c₀|≤K) (hend : |cend|≤K) :
    ‖(hybridCoupling (E:=E) (U:=U) (V:=V) c₀ cend Q)‖≤K := by
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro x
  rw [hybridCoupling_apply,norm_pack_zero_right]
  have h₀' : ‖c₀ • x.fst.snd‖≤K*‖x.fst‖ := by
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right h₀ (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (WithLp.norm_snd_le E x.fst) hK)
  have hend' : ‖endpointCoupling cend Q x‖≤K*‖x.snd‖ := by
    rw [endpointCoupling_apply,norm_smul,Real.norm_eq_abs,LinearIsometry.norm_map,LinearIsometryEquiv.norm_map]
    exact mul_le_mul_of_nonneg_right hend (norm_nonneg _)
  have ha := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).mpr h₀'
  have hb := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).mpr hend'
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).mp
  rw [norm_sq,mul_pow,norm_sq]
  change ‖c₀ • x.fst.snd‖^2+‖endpointCoupling cend Q x‖^2≤K^2*(‖x.fst‖^2+‖x.snd‖^2)
  nlinarith only [ha,hb]

end Bilevel.EndpointTransportResponse
