import Bilevel.ChiVirtualInverseEquality
import Bilevel.ChiExtensionFullGradient
import Bilevel.ChiConservativeScalar

/-! Exact full lower-gradient replies from the actual local extension germ.
This includes the spectator outer block and the unchanged public bilinear
coupling. A failed Bernoulli reply needs only the inactive germ. -/
noncomputable section
open scoped Topology
namespace Bilevel.ChiPrefixEvaluation
open PrimitiveGeometry ChiExtension PartialLegendre
variable {X U V : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem fullExtensionLower_gradient_eq_of_extension_germ {f g : Joint (Joint X U) V → ℝ}
    (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) (δ ε : NNReal) (hδ : δ<1) (hε : ε<1)
    (hF : ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤(δ:ℝ))
    (hG : ∀ z,‖iteratedFDeriv ℝ 2 g z‖≤(ε:ℝ)) (μ L : ℝ) (q : FullNormalVariables X U V)
    (hlocal : let z := jointSolution (reassociated_gradient_lipschitz hf δ hF) hδ q.fst.fst q.snd
      f =ᶠ[𝓝 (pack (pack q.fst.fst z.fst) z.snd)] g) :
    gradient (fullExtensionLower f hf δ hF hδ μ L) q=
      gradient (fullExtensionLower g hg ε hG hε μ L) q := by
  let z := jointSolution (reassociated_gradient_lipschitz hf δ hF) hδ q.fst.fst q.snd
  have hlocal' : f =ᶠ[𝓝 (associateLeft (pack q.fst.fst z))] g := hlocal
  have hr : reassociate f =ᶠ[𝓝 (pack q.fst.fst z)] reassociate g :=
    hlocal'.comp_tendsto (associateLeft (X:=X) (U:=U) (V:=V)).continuous.continuousAt
  have he := (jointSolution_eq_of_extension_germ hf hg δ ε hδ hε hF hG q.fst.fst q.snd hlocal).1
  have hj : jointGradient (reassociated_gradient_lipschitz hf δ hF) hδ (normalConjugateProjection q)=
      jointGradient (reassociated_gradient_lipschitz hg ε hG) hε (normalConjugateProjection q) := by
    change pack (-(gradient (reassociate f) (pack q.fst.fst z)).fst) z=
      pack (-(gradient (reassociate g) (pack q.fst.fst
        (jointSolution (reassociated_gradient_lipschitz hg ε hG) hε q.fst.fst q.snd))).fst)
        (jointSolution (reassociated_gradient_lipschitz hg ε hG) hε q.fst.fst q.snd)
    rw [← he]
    change pack (-(gradient (reassociate f) (pack q.fst.fst z)).fst) z=
      pack (-(gradient (reassociate g) (pack q.fst.fst z)).fst) z
    rw [hr.gradient_eq]
  rw [(fullExtensionLower_hasGradientAt f hf δ hF hδ μ L q).gradient,
    (fullExtensionLower_hasGradientAt g hg ε hG hε μ L q).gradient,hj]

theorem sampleGradient_eq_of_branch_replies {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    (f f₀ g g₀ : W → ℝ) (p : ℝ) (coin : Bool) (q : W)
    (hzero : gradient f₀ q=gradient g₀ q)
    (hone : coin=true → gradient f q=gradient g q) :
    ChiConservative.sampleGradient f f₀ p coin q=ChiConservative.sampleGradient g g₀ p coin q := by
  cases coin with
  | false => simp only [ChiConservative.sampleGradient,BernoulliOracle.sample,Bool.false_eq_true,
      ↓reduceIte,zero_smul,add_zero,hzero]
  | true => simp only [ChiConservative.sampleGradient,hzero,hone rfl]

end Bilevel.ChiPrefixEvaluation
