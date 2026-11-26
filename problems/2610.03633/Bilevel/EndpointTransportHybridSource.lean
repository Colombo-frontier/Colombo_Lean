import Bilevel.EndpointTransportHybridOperators

/-! Prescribed-budget physical operators for the actual heterogeneous
hybrid lower space. The ordinary gain equals the transported endpoint gain. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre EndpointTransportNormalization
variable {E U V : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def sourceHybridHessian {D : ℕ} (L κ : ℝ) (Q : Rotations (interiors κ) D) :
    HybridVariables U V (interiors κ) D →L[ℝ] HybridVariables U V (interiors κ) D :=
  hybridHessian (3*(L/κ)/2) (L/16) Q

def sourceHybridCoupling {D : ℕ} (L κ : ℝ) (Q : Rotations (interiors κ) D) :
    HybridOuter E U D →L[ℝ] HybridVariables U V (interiors κ) D :=
  hybridCoupling (coupling L κ) (L/4) Q

def sourceHybridTangent {D : ℕ} (L κ : ℝ) (Q : Rotations (interiors κ) D) (x : HybridOuter E U D) :
    HybridTangent U (interiors κ) D := hybridTangentResponse (L/16) (L/4) (EndpointTransportNormalization.gain κ) Q x

omit [InnerProductSpace ℝ E] in
theorem sourceHybridTangent_zero {D : ℕ} (L κ : ℝ) (Q : Rotations (interiors κ) D) :
    sourceHybridTangent (E:=E) (U:=U) L κ Q 0=0 := by
  change pack ((EndpointTransportNormalization.gain κ) • (0:U)) (physicalResponse (L/16) (L/4) Q 0)=0
  rw [smul_zero,physicalResponse_zero]
  rfl

theorem source_hybrid_operator_certificate {D : ℕ} {L κ : ℝ} (hL : 0<L) (hκ : 3200≤κ)
    (Q : Rotations (interiors κ) D) :
    let m := 3*(L/κ)/2
    let H₀ := sourceHybridHessian (U:=U) (V:=V) L κ Q
    let C := sourceHybridCoupling (E:=E) (U:=U) (V:=V) L κ Q
    let S := ChiHybrid.correction H₀ m
    (∀ y z,⟪S y,z⟫=⟪y,S z⟫) ∧ (∀ y,0≤⟪y,S y⟫) ∧
    ‖H₀‖≤L/4 ∧ ‖C‖≤L/4 ∧ 2*m+‖S‖+‖C‖≤L ∧
    (∀ v : V,S (pack (0:HybridTangent U (interiors κ) D) v)=0) ∧
    (∀ x : HybridOuter E U D,m • pack (sourceHybridTangent L κ Q x) (0:V)+
      S (pack (sourceHybridTangent L κ Q x) (0:V))=C x) := by
  dsimp only
  let m := 3*(L/κ)/2
  let H₀ := sourceHybridHessian (U:=U) (V:=V) L κ Q
  let C := sourceHybridCoupling (E:=E) (U:=U) (V:=V) L κ Q
  have hκp : 0<κ := by linarith only [hκ]
  have hμ : 0<L/κ := div_pos hL hκp
  have hm : 0<m := by dsimp [m]; positivity
  have hμL : 9*(L/κ)≤L := by
    have hh := mul_le_mul_of_nonneg_right (show (9:ℝ)≤κ by linarith only [hκ]) hL.le
    rw [show 9*(L/κ)=(9*L)/κ by ring]
    apply (div_le_iff₀ hκp).mpr
    nlinarith only [hh]
  have hmL : m≤L/4 := by dsimp [m]; linarith only [hμL,hμ]
  have hphysical := normalized_physicalHessian hL.le hκ Q
  have hphyscoerce (Y : Physical (interiors κ) D) : m*‖Y‖^2≤⟪Y,physicalHessian (L/16) Q Y⟫ := by
    have hh := hphysical.2 Y
    have hp := mul_nonneg hμ.le (sq_nonneg ‖Y‖)
    change 3*(L/κ)/2*‖Y‖^2≤⟪Y,physicalHessian (L/16) Q Y⟫
    nlinarith only [hh,hp]
  have hHnorm : ‖H₀‖≤L/4 := hybridHessian_norm_bound hm.le hmL Q hphysical.1
  have hCnorm : ‖C‖≤L/4 := by
    apply hybridCoupling_norm_bound Q (by positivity)
    · rw [abs_of_nonneg (coupling_nonneg hL.le hκ)]
      exact (coupling_le hL.le hκ).trans (by linarith only [hL])
    · rw [abs_of_pos (by positivity : 0<L/4)]
  have hsym := hybridHessian_symmetric (U:=U) (V:=V) m (L/16) Q
  have hcoerce := hybridHessian_coercive (U:=U) (V:=V) m (L/16) Q hphyscoerce
  refine ⟨ChiHybrid.correction_symmetric H₀ m hsym,
    ChiHybrid.correction_positive H₀ m hcoerce,hHnorm,hCnorm,?_,?_,?_⟩
  · exact ChiHybrid.correction_transport_smooth_budget H₀ C hμ hμL hHnorm hCnorm
  · exact ChiHybrid.correction_kills_normal H₀ m (hybridHessian_on_normal m (L/16) Q)
  · apply ChiHybrid.correction_response_equation H₀ m C (sourceHybridTangent L κ Q)
    intro x
    exact hybrid_response_equation (by positivity : L/16≠0)
      (by rfl : m*EndpointTransportNormalization.gain κ=coupling L κ) Q x

end Bilevel.EndpointTransportResponse
