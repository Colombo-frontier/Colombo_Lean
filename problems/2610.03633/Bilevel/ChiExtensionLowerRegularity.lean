import Bilevel.ChiExtensionResponse
import Bilevel.PartialLegendreExactBudget

/-! Actual complete lower-primitive regularity directly from extension jets,
with the prescribed L and rho budgets and no assumed Hessian formula. -/
noncomputable section
namespace Bilevel.ChiExtension
open PrimitiveGeometry PartialLegendre
variable {X U V : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

def fullExtensionLower (f : Joint (Joint X U) V → ℝ) (hf : ContDiff ℝ 3 f)
    (δ : NNReal) (hb : ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤(δ:ℝ)) (hδ : δ<1)
    (μ L : ℝ) (q : FullNormalVariables X U V) : ℝ :=
  extensionLower f hf δ hb hδ (3*μ/2) (L/4) q.fst.fst q.fst.snd q.snd

theorem fullExtensionLower_regular (f : Joint (Joint X U) V → ℝ) (hf : ContDiff ℝ 3 f)
    (δ : NNReal) (hb : ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤(δ:ℝ)) (hδ : δ<1)
    (hsmall : (δ:ℝ)≤1/12) (μ L ρ : ℝ) (hμ : 0<μ) (hμL : 2*μ≤L) (hρ : 0≤ρ)
    (hthird : ∀ z,‖iteratedFDeriv ℝ 3 f z‖≤ρ/(3*(3*μ/2))) :
    ∃ K : FullNormalVariables X U V → FullNormalVariables X U V →L[ℝ] FullNormalVariables X U V,
      ContDiff ℝ 2 (fullExtensionLower f hf δ hb hδ μ L) ∧
      (∀ q,HasFDerivAt (gradient (fullExtensionLower f hf δ hb hδ μ L)) (K q) q) ∧
      (∀ q,‖K q‖≤L) ∧
      (∀ q r,‖K q-K r‖≤ρ*‖q-r‖) ∧
      (∀ q r,‖gradient (fullExtensionLower f hf δ hb hδ μ L) q-
        gradient (fullExtensionLower f hf δ hb hδ μ L) r‖≤L*‖q-r‖) := by
  let P := reassociate f
  have hP : ContDiff ℝ 3 P := reassociate_contDiff hf
  let B := fderiv ℝ (gradient P)
  have hDG : ∀ z,HasFDerivAt (gradient P) (B z) z := fun z =>
    (((GradientJetBounds.gradient_contDiff hP).differentiable (by norm_num)) z).hasFDerivAt
  let H := ρ/(3*(3*μ/2))
  have hH : 0≤H := by dsimp [H];positivity
  have hLip : ∀ z w,‖B z-B w‖≤H*‖z-w‖ :=
    GradientJetBounds.hessian_lipschitz hP H
      (fun z => (reassociate_jet_bound hf z 3 (by norm_num)).trans (hthird _))
  obtain ⟨K,hC,hD,hN,hV,hG⟩ := fullJointNormalLower_exact_budget
    (reassociated_gradient_lipschitz hf δ hb) hδ P hsmall
    (fun z => ((hP.differentiable (by norm_num)) z).hasGradientAt) B hDG hH hLip hμ hμL
  refine ⟨K,hC,hD,hN,?_,hG⟩
  intro q r
  have hh := hV q r
  have he : 9*μ*H/2=ρ := by dsimp only [H];field_simp;ring
  rwa [he] at hh

end Bilevel.ChiExtension
