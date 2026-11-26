import Bilevel.EndpointTransportHybridPrimitive
import Bilevel.EndpointTransportUpperReadout
import Bilevel.ChiExtensionReadoutGradient
import Bilevel.ChiExtensionCertificateIndependence

/-! Public normal readout and certificate-independent hybrid scalar.
These identities identify the source formula with the compiler's scalar;
they make no statement about revealed information or execution histories. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.PartialLegendre
open PrimitiveGeometry
variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

omit [CompleteSpace X] in
theorem hybridLower_certificate_eq {G : Joint X Y → Joint X Y} {a b : NNReal}
    (hG : LipschitzWith a G) (ha : a<1) (hG' : LipschitzWith b G) (hb : b<1)
    (F : Joint X Y → ℝ) (m : ℝ) (Q : Y →L[ℝ] Y) (C : X →L[ℝ] Y) :
    hybridLower hG ha F m Q C=hybridLower hG' hb F m Q C := by
  funext z
  unfold hybridLower
  rw [jointConjugate_certificate_eq hG ha hG' hb F]

end Bilevel.PartialLegendre

namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre ChiExtension
variable {E U T : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [CompleteSpace T]

omit [CompleteSpace E] [CompleteSpace U] [CompleteSpace T] in
theorem physicalUpper_public_normal {D s : ℕ} (base : Joint E T → ℝ) (dn : ℝ)
    (z : Joint (HybridOuter E U D) (Joint T (Normals s))) :
    physicalUpper base (dn • normalOnes s) z=
      base (pack z.fst.fst.fst z.snd.fst)+dn*normalReadout s z.snd.snd := by
  rw [physicalUpper_apply,real_inner_smul_left]
  have hn := congrArg (fun f : Normals s →L[ℝ] ℝ => f z.snd.snd) (normalOnes_toDual s)
  simpa only [InnerProductSpace.toDual_apply] using congrArg (fun x => base (pack z.fst.fst.fst z.snd.fst)+dn*x) hn

theorem sourceHybridLower_certificate {D s : ℕ} (L κ : ℝ)
    (Q : Rotations (EndpointTransportNormalization.interiors κ) D)
    (F : Joint (HybridOuter E U D) (HybridVariables U (Normals s) (EndpointTransportNormalization.interiors κ) D) → ℝ)
    (hF : ContDiff ℝ 3 F) (a b : NNReal)
    (h2 : ∀ z,‖iteratedFDeriv ℝ 2 F z‖≤(a:ℝ)) (ha : a<1)
    (hG : LipschitzWith b (gradient F)) (hb : b<1) :
    sourceHybridLower L κ Q F hF a h2 ha=
      hybridLower hG hb F (3*(L/κ)/2)
        (ChiHybrid.correction (hybridHessian (3*(L/κ)/2) (L/16) Q) (3*(L/κ)/2))
        (hybridCoupling (EndpointTransportNormalization.coupling L κ) (L/4) Q) :=
  hybridLower_certificate_eq (ChiHybrid.extensionGradientLipschitz F hF a h2) ha hG hb F _ _ _

end Bilevel.EndpointTransportResponse
