import Bilevel.EndpointTransportVirtualGerm
import Bilevel.EndpointTransportHybridFormula

/-! Full physical partial-conjugate inverse/reply equality from a core germ.
The macro is retained, spectator outer variables are kept, and the inverse
input is the original lower query. Public quadratic terms are added later. -/
noncomputable section
set_option maxHeartbeats 800000
open scoped Topology
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre ChiExtension
variable {E U T V : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [CompleteSpace T]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem physical_jointGradient_eq_of_core_germ {D : ℕ} {f g : Joint (Joint E T) V → ℝ}
    {δ ε : NNReal} (hδ : δ<1) (hε : ε<1)
    (hF : LipschitzWith δ (gradient (physicalExtension (U:=U) (D:=D) f)))
    (hG : LipschitzWith ε (gradient (physicalExtension (U:=U) (D:=D) g)))
    (x : HybridOuter E U D) (y : Joint T V)
    (hlocal : let z := jointSolution hF hδ x y
      f =ᶠ[𝓝 (pack (pack x.fst.fst z.fst) z.snd)] g) :
    jointSolution hF hδ x y=jointSolution hG hε x y ∧
      jointGradient hF hδ (pack x y)=jointGradient hG hε (pack x y) := by
  let z := jointSolution hF hδ x y
  have hlocal' : f =ᶠ[𝓝 (normalCoordinates (pack x z))] g := hlocal
  have hext : physicalExtension (U:=U) (D:=D) f =ᶠ[𝓝 (pack x z)] physicalExtension g :=
    hlocal'.comp_tendsto (normalCoordinates (E:=E) (U:=U) (T:=T) (V:=V) (D:=D)).continuous.continuousAt
  have he : z=jointSolution hG hε x y := by
    apply jointSolution_of_equation
    rw [← hext.gradient_eq]
    exact jointSolution_equation hF hδ x y
  refine ⟨he,?_⟩
  change pack (-(gradient (physicalExtension f) (pack x z)).fst) z=
    pack (-(gradient (physicalExtension g) (pack x (jointSolution hG hε x y))).fst)
      (jointSolution hG hε x y)
  rw [← he,hext.gradient_eq]

theorem physical_hybridLower_gradient_eq_of_core_germ {D : ℕ} {f g : Joint (Joint E T) V → ℝ}
    (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) {δ ε : NNReal} (hδ : δ<1) (hε : ε<1)
    (hF : LipschitzWith δ (gradient (physicalExtension (U:=U) (D:=D) f)))
    (hG : LipschitzWith ε (gradient (physicalExtension (U:=U) (D:=D) g)))
    (m : ℝ) (B : Joint T V →L[ℝ] Joint T V) (C : HybridOuter E U D →L[ℝ] Joint T V)
    (hB : B.IsSymmetric) (w : Joint (HybridOuter E U D) (Joint T V))
    (hlocal : let z := jointSolution hF hδ w.fst w.snd
      f =ᶠ[𝓝 (pack (pack w.fst.fst.fst z.fst) z.snd)] g) :
    gradient (hybridLower hF hδ (physicalExtension f) m B C) w=
      gradient (hybridLower hG hε (physicalExtension g) m B C) w := by
  have he := (physical_jointGradient_eq_of_core_germ hδ hε hF hG w.fst w.snd hlocal).2
  rw [hybridLower_gradient hF hδ (physicalExtension f)
      (fun z => ((physicalExtension_contDiff (U:=U) (D:=D) hf).differentiable (by norm_num) z).hasGradientAt) m B C hB,
    hybridLower_gradient hG hε (physicalExtension g)
      (fun z => ((physicalExtension_contDiff (U:=U) (D:=D) hg).differentiable (by norm_num) z).hasGradientAt) m B C hB]
  have hw : pack w.fst w.snd=w := rfl
  rw [hw] at he
  rw [he]

end Bilevel.EndpointTransportResponse
