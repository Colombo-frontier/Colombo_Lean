import Bilevel.BernoulliOracle
import Bilevel.FreshOracle

/-! A globally fixed two-scalar conservative oracle on the entire query
space. Unbiasedness, variance and adaptive centering concern full gradients. -/
noncomputable section
open MeasureTheory
namespace Bilevel.ChiConservative
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

def samplePotential (g g₀ : W → ℝ) (p : ℝ) (b : Bool) (z : W) : ℝ :=
  BernoulliOracle.sample p (g₀ z) (g z-g₀ z) b

def sampleGradient (g g₀ : W → ℝ) (p : ℝ) (b : Bool) (z : W) : W :=
  BernoulliOracle.sample p (gradient g₀ z) (gradient g z-gradient g₀ z) b

theorem sample_hasGradientAt (g g₀ : W → ℝ) (hg : Differentiable ℝ g) (hg₀ : Differentiable ℝ g₀)
    (p : ℝ) (b : Bool) (z : W) :
    HasGradientAt (samplePotential g g₀ p b) (sampleGradient g g₀ p b z) z := by
  apply BernoulliOracle.sample_hasGradient (hg₀ z).hasGradientAt
  apply hasGradientAt_iff_hasFDerivAt.mpr
  simpa only [map_sub] using (hg z).hasGradientAt.hasFDerivAt.sub (hg₀ z).hasGradientAt.hasFDerivAt

theorem sample_gradient (g g₀ : W → ℝ) (hg : Differentiable ℝ g) (hg₀ : Differentiable ℝ g₀)
    (p : ℝ) (b : Bool) (z : W) :
    gradient (samplePotential g g₀ p b) z=sampleGradient g g₀ p b z :=
  (sample_hasGradientAt g g₀ hg hg₀ p b z).gradient

theorem sample_mean (g g₀ : W → ℝ) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (z : W) :
    (∫ b,sampleGradient g g₀ p b z ∂BernoulliOracle.law p hp1)=gradient g z := by
  unfold sampleGradient
  rw [BernoulliOracle.sample_mean p hp hp1]
  abel

theorem sample_variance {g g₀ : W → ℝ} {B σ : ℝ} (hB : 0 < B)
    (henv : ∀ z,‖gradient g z-gradient g₀ z‖ ≤ B) (z : W) :
    (∫ b,‖sampleGradient g g₀ (BernoulliOracle.probability B σ) b z-gradient g z‖^2
      ∂BernoulliOracle.law (BernoulliOracle.probability B σ) (BernoulliOracle.probability_le_one hB)) ≤ σ^2 := by
  have hh := BernoulliOracle.bounded_variance (σ:=σ) hB (gradient g₀ z) (gradient g z-gradient g₀ z) (henv z)
  have he : gradient g₀ z+(gradient g z-gradient g₀ z)=gradient g z := by abel
  simpa only [he,sampleGradient] using hh

variable [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]

theorem sample_measurable (g g₀ : W → ℝ) (hg : Continuous (gradient g)) (hg₀ : Continuous (gradient g₀)) (p : ℝ) :
    Measurable (fun qb : W × Bool => sampleGradient g g₀ p qb.2 qb.1) := by
  have hb : Measurable (fun qb : W × Bool => gradient g₀ qb.1) := hg₀.measurable.comp measurable_fst
  have hs : Measurable (fun qb : W × Bool => gradient g qb.1-gradient g₀ qb.1) :=
    (hg.sub hg₀).measurable.comp measurable_fst
  have hc : Measurable (fun qb : W × Bool => if qb.2 then p⁻¹ else (0:ℝ)) :=
    (measurable_of_finite (fun b : Bool => if b then p⁻¹ else (0:ℝ))).comp measurable_snd
  exact hb.add (hc.smul hs)

def freshOracle (g g₀ : W → ℝ) (hg : Continuous (gradient g)) (hg₀ : Continuous (gradient g₀))
    {B σ : ℝ} (hB : 0 < B) (henv : ∀ z,‖gradient g z-gradient g₀ z‖ ≤ B) :
    FreshOracle.Oracle (Query:=W) (E:=W)
      (BernoulliOracle.law (BernoulliOracle.probability B σ) (BernoulliOracle.probability_le_one hB)) σ where
  truth := gradient g
  sample z b := sampleGradient g g₀ (BernoulliOracle.probability B σ) b z
  truth_measurable := hg.measurable
  sample_measurable := sample_measurable g g₀ hg hg₀ _
  square_integrable _ := Integrable.of_finite
  mean z := by
    rw [integral_sub Integrable.of_finite (integrable_const _),
      sample_mean g g₀ _ (BernoulliOracle.probability_pos hB)]
    simp only [integral_const,measureReal_univ_eq_one,one_smul,sub_self]
  variance := sample_variance hB henv

theorem freshOracle_conservative (g g₀ : W → ℝ) (hd : Differentiable ℝ g) (hd₀ : Differentiable ℝ g₀)
    (hg : Continuous (gradient g)) (hg₀ : Continuous (gradient g₀)) {B σ : ℝ}
    (hB : 0 < B) (henv : ∀ z,‖gradient g z-gradient g₀ z‖ ≤ B) (z : W) (b : Bool) :
    (freshOracle g g₀ hg hg₀ (σ:=σ) hB henv).sample z b=
      gradient (samplePotential g g₀ (BernoulliOracle.probability B σ) b) z :=
  (sample_gradient g g₀ hd hd₀ _ b z).symm

end Bilevel.ChiConservative
