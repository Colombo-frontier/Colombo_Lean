import Bilevel.ChiFullDisclosureFormula
import Bilevel.ChiFullDisclosureState
import Bilevel.ChiExtensionCertificateIndependence

/-! Exact full-column representation of both globally fixed original
normal extensions, with explicit invariance under contraction certificates. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiOuter ChiExtension
variable {E F A : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def originalPotential (active : Bool) (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ)
    (c v : ℝ) (hc : 0<c) (hβ : 0<(D J []).width) (hv : 1≤v) (s : ℕ)
    (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ) (dn : ℝ) :
    Full (Joint E (Blocks m F)) s → ℝ :=
  if active then hierarchyExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn
  else hierarchyInactiveExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn

theorem statePotential_full_frame (active : Bool) (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ)
    (c v : ℝ) (hc : 0<c) (hβ : 0<(D J []).width) (hv : 1≤v) (s : ℕ)
    (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ) (dn : ℝ)
    (UM : A → Space M.n →ₗᵢ[ℝ] E) (U : A → ∀ j I,Space (D j I).n →ₗᵢ[ℝ] F) (a : A) :
    statePotential active m M D J (fun _ => M.n+1) (fun _ => fullCounts D)
      c v s index radialIndex fineIndex rad R dn (fullFrameState M D UM U a)=
    originalPotential active m (reframeNode M (UM a)) (reframeGeometry D (U a)) J
      c v hc hβ hv s index radialIndex fineIndex rad R dn := by
  rw [← statePotential_reframe D (U a) m M (UM a)]
  funext z
  cases active with
  | false =>
    exact virtualInactive_full m (reframeNode M (UM a)) (reframeGeometry D (U a))
      J c v hc hβ hv s index radialIndex fineIndex rad R dn z
  | true =>
    exact virtualActive_full m (reframeNode M (UM a)) (reframeGeometry D (U a))
      J c v hc hβ hv s index radialIndex fineIndex rad R dn z

end Bilevel.ChiPrefixEvaluation

namespace Bilevel.ChiExtension
open PrimitiveGeometry
variable {X U V : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem fullExtensionLower_congr {f g : Joint (Joint X U) V → ℝ} (he : f=g)
    (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) (δ ε : NNReal)
    (hb : ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤(δ:ℝ)) (hδ : δ<1)
    (hb' : ∀ z,‖iteratedFDeriv ℝ 2 g z‖≤(ε:ℝ)) (hε : ε<1) (μ L : ℝ) :
    fullExtensionLower f hf δ hb hδ μ L=fullExtensionLower g hg ε hb' hε μ L := by
  subst g
  exact fullExtensionLower_certificate_eq f hf hg δ ε hb hδ hb' hε μ L

end Bilevel.ChiExtension
