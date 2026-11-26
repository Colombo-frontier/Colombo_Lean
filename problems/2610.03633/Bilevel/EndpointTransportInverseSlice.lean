import Bilevel.EndpointTransportNormalSpace
import Bilevel.ChiHybridExtension
import Bilevel.ChiExtensionRestrictedInverse

/-! Exact physical partial inverse equals the macro-fixed core inverse.
The extra ordinary/endpoint outer coordinates are spectators of the core. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre ChiExtension NearIdentityInverse
variable {E U T V : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [CompleteSpace T]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem physicalExtension_lower_gradient {D : ℕ} {f : Joint (Joint E T) V → ℝ}
    (hf : ContDiff ℝ 3 f) (x : HybridOuter E U D) (y : Joint T V) :
    (gradient (physicalExtension f) (pack x y)).snd=gradient (lowerSlice f x.fst.fst) y := by
  have h := (((physicalExtension_contDiff (U:=U) (D:=D) hf).differentiable (by norm_num)) (pack x y)).hasGradientAt
  exact (PrimitiveGeometry.partial_y h).gradient.symm

theorem physicalExtension_jointSolution {D : ℕ} {f : Joint (Joint E T) V → ℝ}
    (hf : ContDiff ℝ 3 f) (δ : NNReal) (hb : ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤(δ:ℝ)) (hδ : δ<1)
    (hG : LipschitzWith δ (gradient (physicalExtension (U:=U) (D:=D) f)))
    (x : HybridOuter E U D) (y : Joint T V) :
    jointSolution hG hδ x y=solution hδ (lowerSlice_gradient_lipschitz hf δ hb x.fst.fst) y := by
  apply Eq.symm
  apply jointSolution_of_equation hG hδ x y
  rw [physicalExtension_lower_gradient hf]
  exact solution_equation hδ (lowerSlice_gradient_lipschitz hf δ hb x.fst.fst) y

theorem physicalExtension_restricted_inverse {D : ℕ} {f : Joint (Joint E T) V → ℝ}
    (hf : ContDiff ℝ 3 f) (δ : NNReal) (hb : ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤(δ:ℝ)) (hδ : δ<1)
    (hG : LipschitzWith δ (gradient (physicalExtension (U:=U) (D:=D) f)))
    (W : Submodule ℝ (Joint T V)) [CompleteSpace W] (x : HybridOuter E U D) (y : W)
    (hsupport : gradient (lowerSlice f x.fst.fst)
      (restrictedInverse W hδ (lowerSlice_gradient_lipschitz hf δ hb x.fst.fst) y ⟨1,by norm_num⟩)∈W) :
    (restrictedInverse W hδ (lowerSlice_gradient_lipschitz hf δ hb x.fst.fst) y ⟨1,by norm_num⟩ : Joint T V)=
      jointSolution hG hδ x (y:Joint T V) := by
  rw [physicalExtension_jointSolution hf δ hb hδ hG x (y:Joint T V)]
  exact restrictedInverse_eq_full_of_gradient_mem W hδ
    (lowerSlice_gradient_lipschitz hf δ hb x.fst.fst) y ⟨1,by norm_num⟩ hsupport

theorem physicalExtension_inverse_mem {D : ℕ} {f : Joint (Joint E T) V → ℝ}
    (hf : ContDiff ℝ 3 f) (δ : NNReal) (hb : ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤(δ:ℝ)) (hδ : δ<1)
    (hG : LipschitzWith δ (gradient (physicalExtension (U:=U) (D:=D) f)))
    (W : Submodule ℝ (Joint T V)) [CompleteSpace W] (x : HybridOuter E U D) (y : Joint T V)
    (hy : y∈W) (hsupport : ∀ z : W,gradient (lowerSlice f x.fst.fst) z∈W) :
    jointSolution hG hδ x y∈W := by
  rw [← physicalExtension_restricted_inverse hf δ hb hδ hG W x ⟨y,hy⟩ (hsupport _)]
  exact (restrictedInverse W hδ (lowerSlice_gradient_lipschitz hf δ hb x.fst.fst) ⟨y,hy⟩ ⟨1,by norm_num⟩).property

end Bilevel.EndpointTransportResponse
