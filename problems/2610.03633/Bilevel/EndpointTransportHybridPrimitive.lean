import Bilevel.EndpointTransportHybridSource
import Bilevel.ChiHybridExtension

/-! The actual transport hybrid lower Primitive, with the physical response
operator and PSD quadratic correction instantiated at the source scales.
The remaining hypotheses are actual jets of the extension and upper scalar. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre EndpointTransportNormalization
variable {E U V : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

def sourceHybridLower {D : ℕ} (L κ : ℝ) (Q : Rotations (interiors κ) D)
    (P : Joint (HybridOuter E U D) (HybridVariables U V (interiors κ) D) → ℝ)
    (hP : ContDiff ℝ 3 P) (δ : NNReal)
    (h2 : ∀ z,‖iteratedFDeriv ℝ 2 P z‖≤(δ:ℝ)) (hδ : δ<1) :=
  ChiHybrid.lowerOfExtension P hP δ h2 hδ (3*(L/κ)/2)
    (ChiHybrid.correction (sourceHybridHessian L κ Q) (3*(L/κ)/2)) (sourceHybridCoupling L κ Q)

theorem source_hybrid_primitive_of_jets {D : ℕ} {L κ ρ : ℝ}
    (hL : 0<L) (hκ : 3200≤κ) (hρ : 0≤ρ) (Q : Rotations (interiors κ) D)
    (P : Joint (HybridOuter E U D) (HybridVariables U V (interiors κ) D) → ℝ)
    (hP : ContDiff ℝ 3 P) (δ : NNReal)
    (h2 : ∀ z,‖iteratedFDeriv ℝ 2 P z‖≤(δ:ℝ)) (hδ : δ<1) (hsmall : (δ:ℝ)≤1/12)
    (hzero : ∀ x p,P (pack x (pack p (0:V)))=0)
    (h3 : ∀ z,‖iteratedFDeriv ℝ 3 P z‖≤ρ/(3*(3*(L/κ)/2)))
    (f : Joint (HybridOuter E U D) (HybridVariables U V (interiors κ) D) → ℝ)
    (hf : ContDiff ℝ 3 f) (hf2 : ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤L)
    (hfy : ∀ x y,‖gradient (fun w => f (pack x w)) y‖≤L) :
    ∃ Pr : Model.Primitive (X:=HybridOuter E U D) (Y:=HybridVariables U V (interiors κ) D)
        (L/κ) L L L ρ,
      (∀ x y,Pr.f x y=f (pack x y)) ∧
      (∀ x y,Pr.g x y=sourceHybridLower L κ Q P hP δ h2 hδ (pack x y)) ∧
      ∃ r : Pr.Response,
        (∀ x,r.y x=ChiHybrid.responseOfExtension P (sourceHybridTangent L κ Q) x) ∧
        (∀ x,Pr.hyperobjective r x=f (pack x (ChiHybrid.responseOfExtension P (sourceHybridTangent L κ Q) x))) ∧
        (∀ x y,Pr.IsLowerSolution x y ↔ y=ChiHybrid.responseOfExtension P (sourceHybridTangent L κ Q) x) := by
  have hκp : 0<κ := by linarith only [hκ]
  have hμ : 0<L/κ := div_pos hL hκp
  have hm : 0<3*(L/κ)/2 := by positivity
  obtain ⟨hsym,hpsd,_hH,_hC,hsmooth,hkill,hlinear⟩ :=
    source_hybrid_operator_certificate (E:=E) (U:=U) (V:=V) hL hκ Q
  have hmodulus : L/κ≤(3*(L/κ)/2)/(1+(δ:ℝ)) := by
    apply (le_div_iff₀ (show 0<1+(δ:ℝ) by positivity)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hsmall hμ.le,hμ]
  exact ChiHybrid.hybrid_primitive_of_extension_jets P hP δ h2 hδ
    (by linarith only [hsmall]) hzero (3*(L/κ)/2) hm
    (ChiHybrid.correction (sourceHybridHessian L κ Q) (3*(L/κ)/2)) (sourceHybridCoupling L κ Q)
    hsym hpsd (sourceHybridTangent L κ Q) hkill hlinear f hf
    (L/κ) L L L ρ hμ hL.le hL.le hL.le hρ hmodulus hsmooth h3 hf2 hfy

end Bilevel.EndpointTransportResponse
