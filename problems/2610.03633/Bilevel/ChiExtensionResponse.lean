import Bilevel.ChiExtensionReassociate
import Bilevel.PartialLegendreJointResponse
import Bilevel.GradientJetBounds

/-! Actual partial-Legendre lower primitive for an extension in the concrete
normal-coordinate product. Smallness enters through the proved Hessian norm,
not through an assumed response or inverse. -/
noncomputable section
namespace Bilevel.ChiExtension
open PrimitiveGeometry PartialLegendre
variable {X U V : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem reassociated_gradient_lipschitz {f : Joint (Joint X U) V → ℝ} (hf : ContDiff ℝ 3 f)
    (δ : NNReal) (hb : ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤(δ:ℝ)) :
    LipschitzWith δ (gradient (reassociate f)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simpa only [dist_eq_norm] using GradientJetBounds.gradient_lipschitz (reassociate_contDiff hf) δ
    (fun z => (reassociate_jet_bound hf z 2 (by norm_num)).trans (hb _)) z w

def normalTrace (f : Joint (Joint X U) V → ℝ) (x : X) (u : U) : V :=
  gradient (fun q : V => f (pack (pack x u) q)) 0

theorem reassociated_normal_gradient {f : Joint (Joint X U) V → ℝ} (hf : ContDiff ℝ 3 f)
    (x : X) (u : U) :
    (gradient (reassociate f) (pack x (pack u (0:V)))).snd.snd=normalTrace f x u := by
  have hg := (((reassociate_contDiff hf).differentiable (by norm_num)) (pack x (pack u (0:V)))).hasGradientAt
  have hs := PrimitiveGeometry.partial_y (PrimitiveGeometry.partial_y hg)
  exact hs.gradient.symm

def extensionLower (f : Joint (Joint X U) V → ℝ) (hf : ContDiff ℝ 3 f)
    (δ : NNReal) (hb : ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤(δ:ℝ)) (hδ : δ<1)
    (m c : ℝ) (x : X) (v : U) (y : Joint U V) : ℝ :=
  jointNormalLower (reassociated_gradient_lipschitz hf δ hb) hδ (reassociate f) m c x v y

theorem extensionLower_unique_response (f : Joint (Joint X U) V → ℝ) (hf : ContDiff ℝ 3 f)
    (δ : NNReal) (hb : ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤(δ:ℝ)) (hδ : δ<1)
    (hzero : ∀ p,f (pack p (0:V))=0) {m : ℝ} (hm : 0<m) (c : ℝ)
    (x : X) (v : U) (y : Joint U V) :
    (∀ w,extensionLower f hf δ hb hδ m c x v y≤extensionLower f hf δ hb hδ m c x v w) ↔
      y=pack ((c/m) • v) (normalTrace f x ((c/m) • v)) := by
  exact jointNormalLower_unique_response (reassociated_gradient_lipschitz hf δ hb) hδ (reassociate f)
    (fun z => (((reassociate_contDiff hf).differentiable (by norm_num)) z).hasGradientAt)
    (fun x p => hzero (pack x p)) (normalTrace f) (reassociated_normal_gradient hf) hm c x v y

theorem extensionLower_response_minimizes (f : Joint (Joint X U) V → ℝ) (hf : ContDiff ℝ 3 f)
    (δ : NNReal) (hb : ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤(δ:ℝ)) (hδ : δ<1)
    (hzero : ∀ p,f (pack p (0:V))=0) {m : ℝ} (hm : 0<m) (c : ℝ)
    (x : X) (v : U) (y : Joint U V) :
    extensionLower f hf δ hb hδ m c x v (pack ((c/m) • v) (normalTrace f x ((c/m) • v)))≤
      extensionLower f hf δ hb hδ m c x v y :=
  (extensionLower_unique_response f hf δ hb hδ hzero hm c x v _).mpr rfl y

end Bilevel.ChiExtension
