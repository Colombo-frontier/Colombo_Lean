import Bilevel.ChiExtensionLowerRegularity

/-! The actual inverse and partial conjugate do not depend on which valid
contraction bound certifies them. Different numeric bounds are identified by
the inverse equation and uniqueness, rather than by proof irrelevance. -/
noncomputable section
namespace Bilevel.PartialLegendre
open PrimitiveGeometry
variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

omit [CompleteSpace X] in
theorem jointSolution_certificate_eq {G : Joint X Y → Joint X Y} {δ ε : NNReal}
    (hG : LipschitzWith δ G) (hδ : δ<1) (hG' : LipschitzWith ε G) (hε : ε<1)
    (x : X) (y : Y) : jointSolution hG hδ x y=jointSolution hG' hε x y :=
  jointSolution_of_equation hG' hε x y _ (jointSolution_equation hG hδ x y)

omit [CompleteSpace X] in
theorem jointConjugate_certificate_eq {G : Joint X Y → Joint X Y} {δ ε : NNReal}
    (hG : LipschitzWith δ G) (hδ : δ<1) (hG' : LipschitzWith ε G) (hε : ε<1)
    (P : Joint X Y → ℝ) : jointConjugate hG hδ P=jointConjugate hG' hε P := by
  funext q
  rw [jointConjugate_value,jointConjugate_value,jointSolution_certificate_eq hG hδ hG' hε]

end Bilevel.PartialLegendre

namespace Bilevel.ChiExtension
open PrimitiveGeometry PartialLegendre
variable {X U V : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem extensionLower_certificate_eq (f : Joint (Joint X U) V → ℝ)
    (hf hf' : ContDiff ℝ 3 f) (δ ε : NNReal)
    (hb : ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤(δ:ℝ)) (hδ : δ<1)
    (hb' : ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤(ε:ℝ)) (hε : ε<1)
    (m c : ℝ) : extensionLower f hf δ hb hδ m c=extensionLower f hf' ε hb' hε m c := by
  funext x v y
  unfold extensionLower jointNormalLower
  rw [jointConjugate_certificate_eq (reassociated_gradient_lipschitz hf δ hb) hδ
    (reassociated_gradient_lipschitz hf' ε hb') hε]

theorem fullExtensionLower_certificate_eq (f : Joint (Joint X U) V → ℝ)
    (hf hf' : ContDiff ℝ 3 f) (δ ε : NNReal)
    (hb : ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤(δ:ℝ)) (hδ : δ<1)
    (hb' : ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤(ε:ℝ)) (hε : ε<1)
    (μ L : ℝ) : fullExtensionLower f hf δ hb hδ μ L=fullExtensionLower f hf' ε hb' hε μ L := by
  funext q
  unfold fullExtensionLower
  rw [extensionLower_certificate_eq f hf hf' δ ε hb hδ hb' hε]

theorem fullExtensionLower_gradient_certificate_eq (f : Joint (Joint X U) V → ℝ)
    (hf hf' : ContDiff ℝ 3 f) (δ ε : NNReal)
    (hb : ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤(δ:ℝ)) (hδ : δ<1)
    (hb' : ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤(ε:ℝ)) (hε : ε<1)
    (μ L : ℝ) (q : FullNormalVariables X U V) :
    gradient (fullExtensionLower f hf δ hb hδ μ L) q=
      gradient (fullExtensionLower f hf' ε hb' hε μ L) q := by
  rw [fullExtensionLower_certificate_eq f hf hf' δ ε hb hδ hb' hε]

end Bilevel.ChiExtension
