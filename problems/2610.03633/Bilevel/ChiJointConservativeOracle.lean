import Bilevel.ChiConservativeCertificate
import Bilevel.ChiUpperNoisePrimitiveOracle

/-! The ordinary hard family uses the complete original SFO pair. The
upper response is the exact nonlinear upper gradient; the lower response
is the fixed conservative Bernoulli sample. Both share the same coin. -/
noncomputable section
open MeasureTheory
namespace Bilevel.ChiPrimitive
open PrimitiveGeometry
variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)]

theorem full_joint_oracles_of_conservative {μ Lf Lg Cf ρ B : ℝ}
    (P : Model.Primitive (X:=X) (Y:=Y) μ Lf Lg Cf ρ)
    (f g g₀ : Joint X Y → ℝ) (hf : ContDiff ℝ 3 f)
    (hg : Differentiable ℝ g) (hg₀ : Differentiable ℝ g₀)
    (hPf : ∀ x y,P.f x y=f (pack x y)) (hO : HasConservativeOracle P g g₀ B)
    (σf σg : ℝ) :
    ∃ hB : 0<B,
    ∃ Of : FreshOracle.Oracle (Query:=Joint X Y) (E:=Joint X Y)
      (BernoulliOracle.law (BernoulliOracle.probability B σg) (BernoulliOracle.probability_le_one hB)) σf,
    ∃ Og : FreshOracle.Oracle (Query:=Joint X Y) (E:=Joint X Y)
      (BernoulliOracle.law (BernoulliOracle.probability B σg) (BernoulliOracle.probability_le_one hB)) σg,
      (∀ z,Of.truth z=pack (P.fx z.fst z.snd) (P.fy z.fst z.snd)) ∧
      (∀ z,Og.truth z=pack (P.gx z.fst z.snd) (P.gy z.fst z.snd)) ∧
      ∀ z coin,(Of.sample z coin,Og.sample z coin)=
        (gradient f z,ChiConservative.sampleGradient g g₀ (BernoulliOracle.probability B σg) coin z) := by
  obtain ⟨hB,Og,ht,hsg⟩ := hO σg
  let Of : FreshOracle.Oracle (Query:=Joint X Y) (E:=Joint X Y)
      (BernoulliOracle.law (BernoulliOracle.probability B σg) (BernoulliOracle.probability_le_one hB)) σf :=
    { truth := gradient f
      sample := fun z _ => gradient f z
      truth_measurable := (GradientJetBounds.gradient_contDiff hf).continuous.measurable
      sample_measurable := (GradientJetBounds.gradient_contDiff hf).continuous.measurable.comp measurable_fst
      square_integrable := by intro z;simp
      mean := by intro z;simp
      variance := by intro z;simp only [sub_self,norm_zero,zero_pow (by norm_num : 2≠0),integral_zero];positivity }
  refine ⟨hB,Of,Og,?_,ht,?_⟩
  · exact fun z => ChiUpperNoise.upper_full_gradient P f (hf.differentiable (by norm_num)) hPf z
  · intro z coin
    rw [hsg,ChiConservative.sample_gradient g g₀ hg hg₀]

end Bilevel.ChiPrimitive
