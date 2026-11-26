import Bilevel.ChiExtensionBoundIndependence
import Bilevel.PartialLegendreFreshOracle

/-! Actual full gradients and informative envelopes on (x,v,u,s). The
spectator outer variable and the public bilinear coupling are retained. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Bilevel.ChiExtension
open PrimitiveGeometry PartialLegendre
variable {X U V : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem fullExtensionLower_hasGradientAt (f : Joint (Joint X U) V → ℝ) (hf : ContDiff ℝ 3 f)
    (δ : NNReal) (hb : ∀ z,‖iteratedFDeriv ℝ 2 f z‖ ≤ (δ:ℝ)) (hδ : δ < 1)
    (μ L : ℝ) (q : FullNormalVariables X U V) :
    HasGradientAt (fullExtensionLower f hf δ hb hδ μ L)
      ((3*μ/2) • normalConjugateProjection.adjoint
        (jointGradient (reassociated_gradient_lipschitz hf δ hb) hδ (normalConjugateProjection q))-
        (L/4) • bilinearCouplingOperator normalOuterProjection normalTangentProjection q) q :=
  conjugateCoupling_hasGradientAt (reassociated_gradient_lipschitz hf δ hb) hδ (reassociate f)
    (fun z => (((reassociate_contDiff hf).differentiable (by norm_num)) z).hasGradientAt)
    normalConjugateProjection normalOuterProjection normalTangentProjection (3*μ/2) (L/4) q

theorem fullExtensionLower_gradient_continuous (f : Joint (Joint X U) V → ℝ) (hf : ContDiff ℝ 3 f)
    (δ : NNReal) (hb : ∀ z,‖iteratedFDeriv ℝ 2 f z‖ ≤ (δ:ℝ)) (hδ : δ < 1) (μ L : ℝ) :
    Continuous (gradient (fullExtensionLower f hf δ hb hδ μ L)) := by
  have he := funext (fun q => (fullExtensionLower_hasGradientAt f hf δ hb hδ μ L q).gradient)
  rw [he]
  let T : FullNormalVariables X U V →L[ℝ] Joint X (Joint U V) := normalConjugateProjection
  let A : FullNormalVariables X U V →L[ℝ] U := normalOuterProjection
  let B : FullNormalVariables X U V →L[ℝ] U := normalTangentProjection
  exact ((T.adjoint.continuous.comp
    ((ConjugateOracle.jointGradient_continuous (reassociated_gradient_lipschitz hf δ hb) hδ).comp T.continuous)).const_smul (3*μ/2)).sub
      ((bilinearCouplingOperator A B).continuous.const_smul (L/4))

theorem reassociated_gradient_difference_bound {f f₀ : Joint (Joint X U) V → ℝ}
    (hf : ContDiff ℝ 3 f) (hf₀ : ContDiff ℝ 3 f₀) {η : ℝ}
    (hjet : ∀ z,‖iteratedFDeriv ℝ 1 (fun q => f q-f₀ q) z‖ ≤ η) (z : Joint X (Joint U V)) :
    ‖gradient (reassociate f) z-gradient (reassociate f₀) z‖ ≤ η := by
  have ha := (((reassociate_contDiff hf).differentiable (by norm_num)) z).hasGradientAt
  have hb := (((reassociate_contDiff hf₀).differentiable (by norm_num)) z).hasGradientAt
  have hd : HasGradientAt (reassociate (fun q => f q-f₀ q))
      (gradient (reassociate f) z-gradient (reassociate f₀) z) z := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    simpa only [map_sub] using ha.hasFDerivAt.sub hb.hasFDerivAt
  rw [← hd.gradient,GradientJetBounds.gradient_norm_eq,← ChiBoundedChain.Composition.norm_first]
  exact (reassociate_jet_bound (hf.sub hf₀) z 1 (by norm_num)).trans (hjet _)

theorem fullExtensionLower_difference_envelope
    (f f₀ : Joint (Joint X U) V → ℝ) (hf : ContDiff ℝ 3 f) (hf₀ : ContDiff ℝ 3 f₀)
    (δ : NNReal) (hb : ∀ z,‖iteratedFDeriv ℝ 2 f z‖ ≤ (δ:ℝ))
    (hb₀ : ∀ z,‖iteratedFDeriv ℝ 2 f₀ z‖ ≤ (δ:ℝ)) (hδ : δ < 1)
    (μ L : ℝ) (hμ : 0 ≤ μ) {η : ℝ}
    (hjet : ∀ z,‖iteratedFDeriv ℝ 1 (fun q => f q-f₀ q) z‖ ≤ η)
    (q : FullNormalVariables X U V) :
    ‖gradient (fullExtensionLower f hf δ hb hδ μ L) q-
      gradient (fullExtensionLower f₀ hf₀ δ hb₀ hδ μ L) q‖ ≤
        (Real.sqrt 2*(3*μ/2)/(1-(δ:ℝ)))*η := by
  rw [(fullExtensionLower_hasGradientAt f hf δ hb hδ μ L q).gradient,
    (fullExtensionLower_hasGradientAt f₀ hf₀ δ hb₀ hδ μ L q).gradient]
  let T : FullNormalVariables X U V →L[ℝ] Joint X (Joint U V) := normalConjugateProjection
  let a := jointGradient (reassociated_gradient_lipschitz hf δ hb) hδ (T q)
  let b := jointGradient (reassociated_gradient_lipschitz hf₀ δ hb₀) hδ (T q)
  have he : (3*μ/2) • T.adjoint a-(L/4) • bilinearCouplingOperator normalOuterProjection normalTangentProjection q-
      ((3*μ/2) • T.adjoint b-(L/4) • bilinearCouplingOperator normalOuterProjection normalTangentProjection q)=
      (3*μ/2) • T.adjoint (a-b) := by rw [map_sub];module
  change ‖(3*μ/2) • T.adjoint a-(L/4) • bilinearCouplingOperator normalOuterProjection normalTangentProjection q-
      ((3*μ/2) • T.adjoint b-(L/4) • bilinearCouplingOperator normalOuterProjection normalTangentProjection q)‖ ≤ _
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ 3*μ/2)]
  have ht : ‖T.adjoint (a-b)‖ ≤ ‖a-b‖ := by
    apply (T.adjoint.le_opNorm (a-b)).trans
    rw [ContinuousLinearMap.adjoint.norm_map]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (normalConjugateProjection_norm (X:=X) (U:=U) (V:=V)) (norm_nonneg (a-b))
  have hd := jointGradient_difference_bound (reassociated_gradient_lipschitz hf δ hb)
    (reassociated_gradient_lipschitz hf₀ δ hb₀) hδ (reassociated_gradient_difference_bound hf hf₀ hjet) (T q)
  have hh := mul_le_mul_of_nonneg_left (ht.trans hd) (show 0 ≤ 3*μ/2 by positivity)
  convert hh using 1
  ring

end Bilevel.ChiExtension
