import Bilevel.ChiExtensionResponse
import Bilevel.ChiCarrierNormalSpace

/-! Exact identification of the source's partial-conjugate inverse with
the near-identity inverse of the actual macro-fixed extension slice. -/
noncomputable section
namespace Bilevel.ChiExtension
open PrimitiveGeometry PartialLegendre
variable {X U V : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

def lowerSlice (f : Joint (Joint X U) V → ℝ) (a : X) (z : Joint U V) : ℝ :=
  f (pack (pack a z.fst) z.snd)

omit [CompleteSpace X] [CompleteSpace U] [CompleteSpace V] in
theorem lowerSlice_contDiff {f : Joint (Joint X U) V → ℝ} (hf : ContDiff ℝ 3 f) (a : X) :
    ContDiff ℝ 3 (lowerSlice f a) :=
  (reassociate_contDiff hf).comp ((packLinear (X:=X) (Y:=Joint U V)).contDiff.comp
    (contDiff_const.prodMk contDiff_id))

theorem lowerSlice_gradient {f : Joint (Joint X U) V → ℝ} (hf : ContDiff ℝ 3 f)
    (a : X) (z : Joint U V) :
    gradient (lowerSlice f a) z=(gradient (reassociate f) (pack a z)).snd := by
  have hg := ((reassociate_contDiff hf).differentiable (by norm_num) (pack a z)).hasGradientAt
  change HasGradientAt (reassociate f) (pack ((gradient (reassociate f) (pack a z)).fst)
    ((gradient (reassociate f) (pack a z)).snd)) (pack a z) at hg
  exact (PrimitiveGeometry.partial_y hg).gradient

theorem lowerSlice_gradient_lipschitz {f : Joint (Joint X U) V → ℝ} (hf : ContDiff ℝ 3 f)
    (δ : NNReal) (hb : ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤(δ:ℝ)) (a : X) :
    LipschitzWith δ (gradient (lowerSlice f a)) := by
  rw [funext (lowerSlice_gradient hf a)]
  exact jointSlice_lipschitz (reassociated_gradient_lipschitz hf δ hb) a

theorem lowerSlice_solution_eq_jointSolution {f : Joint (Joint X U) V → ℝ} (hf : ContDiff ℝ 3 f)
    (δ : NNReal) (hb : ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤(δ:ℝ)) (hδ : δ<1) (a : X) (y : Joint U V) :
    solution hδ (lowerSlice_gradient_lipschitz hf δ hb a) y=
      jointSolution (reassociated_gradient_lipschitz hf δ hb) hδ a y := by
  apply jointSolution_of_equation
  rw [← lowerSlice_gradient hf a]
  exact solution_equation hδ (lowerSlice_gradient_lipschitz hf δ hb a) y

end Bilevel.ChiExtension
