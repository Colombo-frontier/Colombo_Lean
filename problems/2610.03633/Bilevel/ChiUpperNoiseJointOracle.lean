import Bilevel.ChiUpperNoisePrimitiveOracle

/-! The upper-noise branch is a valid complete original SFO pair for any
declared lower variance bound; its lower sample remains exactly public. -/
noncomputable section
open MeasureTheory
namespace Bilevel.ChiUpperNoise
open PrimitiveGeometry
variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)]

theorem full_joint_oracles_of_upper_noise {μ Lf Lg Cf ρ B : ℝ}
    (P : Model.Primitive (X:=X) (Y:=Y) μ Lf Lg Cf ρ)
    (f f₀ g : Joint X Y → ℝ) (hf : Differentiable ℝ f) (hf₀ : Differentiable ℝ f₀)
    (hO : HasUpperNoiseOracle P f f₀ g B) (σf σg : ℝ) :
    ∃ hB : 0<B,
    ∃ Of : FreshOracle.Oracle (Query:=Joint X Y) (E:=Joint X Y)
      (BernoulliOracle.law (BernoulliOracle.probability B σf) (BernoulliOracle.probability_le_one hB)) σf,
    ∃ Og : FreshOracle.Oracle (Query:=Joint X Y) (E:=Joint X Y)
      (BernoulliOracle.law (BernoulliOracle.probability B σf) (BernoulliOracle.probability_le_one hB)) σg,
      (∀ z,Of.truth z=pack (P.fx z.fst z.snd) (P.fy z.fst z.snd)) ∧
      (∀ z,Og.truth z=pack (P.gx z.fst z.snd) (P.gy z.fst z.snd)) ∧
      ∀ z coin,(Of.sample z coin,Og.sample z coin)=
        (ChiConservative.sampleGradient f f₀ (BernoulliOracle.probability B σf) coin z,gradient g z) := by
  obtain ⟨hB,Of,Og,hft,hfs,hgt,hgs⟩ := hO σf
  let Og' : FreshOracle.Oracle (Query:=Joint X Y) (E:=Joint X Y)
      (BernoulliOracle.law (BernoulliOracle.probability B σf) (BernoulliOracle.probability_le_one hB)) σg :=
    { Og with
      variance := by
        intro z
        exact (Og.variance z).trans (by simpa using sq_nonneg σg) }
  refine ⟨hB,Of,Og',hft,hgt,?_⟩
  intro z coin
  change (Of.sample z coin,Og.sample z coin)=_
  rw [hfs,hgs,ChiConservative.sample_gradient f f₀ hf hf₀]

end Bilevel.ChiUpperNoise
