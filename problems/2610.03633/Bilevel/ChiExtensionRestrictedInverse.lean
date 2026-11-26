import Bilevel.ChiExtensionSliceInverse

/-! Exact restricted/full partial-conjugate inverse interface. Gradient
membership is deliberately visible here; the concrete hierarchy support
modules prove it from numerical blind-coordinate and prefix conditions. -/
noncomputable section
namespace Bilevel.ChiExtension
open PrimitiveGeometry PartialLegendre NearIdentityInverse
variable {X U V : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem restricted_lowerSlice_eq_jointSolution
    (W : Submodule ℝ (Joint U V)) [CompleteSpace W]
    {f : Joint (Joint X U) V → ℝ} (hf : ContDiff ℝ 3 f)
    (δ : NNReal) (hb : ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤(δ:ℝ)) (hδ : δ<1)
    (a : X) (u : W)
    (hsupport : gradient (lowerSlice f a)
      (restrictedInverse W hδ (lowerSlice_gradient_lipschitz hf δ hb a) u ⟨1,by norm_num⟩)∈W) :
    (restrictedInverse W hδ (lowerSlice_gradient_lipschitz hf δ hb a) u ⟨1,by norm_num⟩ : Joint U V)=
      jointSolution (reassociated_gradient_lipschitz hf δ hb) hδ a (u:Joint U V) := by
  have he := restrictedInverse_eq_full_of_gradient_mem W hδ (lowerSlice_gradient_lipschitz hf δ hb a)
    u ⟨1,by norm_num⟩ hsupport
  change (restrictedInverse W hδ (lowerSlice_gradient_lipschitz hf δ hb a) u ⟨1,by norm_num⟩ : Joint U V)=
    solution hδ (lowerSlice_gradient_lipschitz hf δ hb a) (u:Joint U V) at he
  exact he.trans (lowerSlice_solution_eq_jointSolution hf δ hb hδ a u)

end Bilevel.ChiExtension
