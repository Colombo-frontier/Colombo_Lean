import Bilevel.ChiExtensionSliceInverse

/-! A genuine full-query scalar germ equality at the actual inverse point
identifies both nonlinear partial inverses and their full-gradient replies.
Construction-specific germ theorems are proved separately. -/
noncomputable section
open scoped Topology
namespace Bilevel.ChiPrefixEvaluation
open PrimitiveGeometry ChiExtension PartialLegendre
variable {X U V : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem jointSolution_eq_of_extension_germ {f g : Joint (Joint X U) V → ℝ}
    (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) (δ ε : NNReal) (hδ : δ<1) (hε : ε<1)
    (hF : ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤(δ:ℝ))
    (hG : ∀ z,‖iteratedFDeriv ℝ 2 g z‖≤(ε:ℝ)) (a : X) (y : Joint U V)
    (hlocal : let z := jointSolution (reassociated_gradient_lipschitz hf δ hF) hδ a y
      f =ᶠ[𝓝 (pack (pack a z.fst) z.snd)] g) :
    jointSolution (reassociated_gradient_lipschitz hf δ hF) hδ a y=
      jointSolution (reassociated_gradient_lipschitz hg ε hG) hε a y ∧
    gradient f (associateLeft (pack a (jointSolution (reassociated_gradient_lipschitz hf δ hF) hδ a y)))=
      gradient g (associateLeft (pack a (jointSolution (reassociated_gradient_lipschitz hg ε hG) hε a y))) := by
  let z := jointSolution (reassociated_gradient_lipschitz hf δ hF) hδ a y
  have hlocal' : f =ᶠ[𝓝 (associateLeft (pack a z))] g := hlocal
  have hr : reassociate f =ᶠ[𝓝 (pack a z)] reassociate g :=
    hlocal'.comp_tendsto (associateLeft (X:=X) (U:=U) (V:=V)).continuous.continuousAt
  have he : z=jointSolution (reassociated_gradient_lipschitz hg ε hG) hε a y := by
    apply jointSolution_of_equation
    rw [← hr.gradient_eq]
    exact jointSolution_equation (reassociated_gradient_lipschitz hf δ hF) hδ a y
  refine ⟨he,?_⟩
  change gradient f (associateLeft (pack a z))=gradient g _
  rw [← he]
  exact hlocal'.gradient_eq

end Bilevel.ChiPrefixEvaluation
