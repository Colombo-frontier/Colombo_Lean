import Bilevel.ChiExtensionFullGradient
import Bilevel.ChiConservativeScalar

/-! Full-query conservative fresh-sample oracle for the actual active and
inactive partial conjugates, allowing their Hessian certificates to differ. -/
noncomputable section
namespace Bilevel.ChiExtension
open PrimitiveGeometry PartialLegendre
variable {X U V : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem fullExtensionLower_two_bound_envelope
    (f f₀ : Joint (Joint X U) V → ℝ) (hf : ContDiff ℝ 3 f) (hf₀ : ContDiff ℝ 3 f₀)
    (a b : NNReal) (hfa : ∀ z,‖iteratedFDeriv ℝ 2 f z‖ ≤ (a:ℝ))
    (hfb : ∀ z,‖iteratedFDeriv ℝ 2 f₀ z‖ ≤ (b:ℝ)) (ha : a < 1) (hb : b < 1)
    (μ L : ℝ) (hμ : 0 ≤ μ) {η : ℝ}
    (hjet : ∀ z,‖iteratedFDeriv ℝ 1 (fun q => f q-f₀ q) z‖ ≤ η)
    (q : FullNormalVariables X U V) :
    ‖gradient (fullExtensionLower f hf a hfa ha μ L) q-
      gradient (fullExtensionLower f₀ hf₀ b hfb hb μ L) q‖ ≤
        (Real.sqrt 2*(3*μ/2)/(1-((max a b):ℝ)))*η := by
  have had : ∀ z,‖iteratedFDeriv ℝ 2 f z‖ ≤ ((max a b):ℝ) :=
    fun z => (hfa z).trans (by exact_mod_cast (le_max_left a b))
  have hbd : ∀ z,‖iteratedFDeriv ℝ 2 f₀ z‖ ≤ ((max a b):ℝ) :=
    fun z => (hfb z).trans (by exact_mod_cast (le_max_right a b))
  have hd : max a b < 1 := max_lt ha hb
  rw [fullExtensionLower_bound_independent f hf a (max a b) hfa had ha hd μ L,
    fullExtensionLower_bound_independent f₀ hf₀ b (max a b) hfb hbd hb hd μ L]
  exact fullExtensionLower_difference_envelope f f₀ hf hf₀ (max a b) had hbd hd μ L hμ hjet q

variable [MeasurableSpace (FullNormalVariables X U V)] [BorelSpace (FullNormalVariables X U V)]
  [SecondCountableTopology (FullNormalVariables X U V)]

def extensionFreshOracle
    (f f₀ : Joint (Joint X U) V → ℝ) (hf : ContDiff ℝ 3 f) (hf₀ : ContDiff ℝ 3 f₀)
    (a b : NNReal) (hfa : ∀ z,‖iteratedFDeriv ℝ 2 f z‖ ≤ (a:ℝ))
    (hfb : ∀ z,‖iteratedFDeriv ℝ 2 f₀ z‖ ≤ (b:ℝ)) (ha : a < 1) (hb : b < 1)
    (μ L : ℝ) (hμ : 0 ≤ μ) {η B σ : ℝ} (hB : 0 < B)
    (hjet : ∀ z,‖iteratedFDeriv ℝ 1 (fun q => f q-f₀ q) z‖ ≤ η)
    (henv : (Real.sqrt 2*(3*μ/2)/(1-((max a b):ℝ)))*η ≤ B) :
    FreshOracle.Oracle (Query:=FullNormalVariables X U V) (E:=FullNormalVariables X U V)
      (BernoulliOracle.law (BernoulliOracle.probability B σ) (BernoulliOracle.probability_le_one hB)) σ :=
  ChiConservative.freshOracle (fullExtensionLower f hf a hfa ha μ L) (fullExtensionLower f₀ hf₀ b hfb hb μ L)
    (fullExtensionLower_gradient_continuous f hf a hfa ha μ L)
    (fullExtensionLower_gradient_continuous f₀ hf₀ b hfb hb μ L) hB
    (fun q => (fullExtensionLower_two_bound_envelope f f₀ hf hf₀ a b hfa hfb ha hb μ L hμ hjet q).trans henv)

theorem extensionFreshOracle_conservative
    (f f₀ : Joint (Joint X U) V → ℝ) (hf : ContDiff ℝ 3 f) (hf₀ : ContDiff ℝ 3 f₀)
    (a b : NNReal) (hfa : ∀ z,‖iteratedFDeriv ℝ 2 f z‖ ≤ (a:ℝ))
    (hfb : ∀ z,‖iteratedFDeriv ℝ 2 f₀ z‖ ≤ (b:ℝ)) (ha : a < 1) (hb : b < 1)
    (μ L : ℝ) (hμ : 0 ≤ μ) {η B σ : ℝ} (hB : 0 < B)
    (hjet : ∀ z,‖iteratedFDeriv ℝ 1 (fun q => f q-f₀ q) z‖ ≤ η)
    (henv : (Real.sqrt 2*(3*μ/2)/(1-((max a b):ℝ)))*η ≤ B)
    (q : FullNormalVariables X U V) (coin : Bool) :
    (extensionFreshOracle f f₀ hf hf₀ a b hfa hfb ha hb μ L hμ (σ:=σ) hB hjet henv).sample q coin=
      gradient (ChiConservative.samplePotential (fullExtensionLower f hf a hfa ha μ L)
        (fullExtensionLower f₀ hf₀ b hfb hb μ L) (BernoulliOracle.probability B σ) coin) q :=
  ChiConservative.freshOracle_conservative _ _
    (fun z => (fullExtensionLower_hasGradientAt f hf a hfa ha μ L z).differentiableAt)
    (fun z => (fullExtensionLower_hasGradientAt f₀ hf₀ b hfb hb μ L z).differentiableAt) _ _ hB _ q coin

end Bilevel.ChiExtension
