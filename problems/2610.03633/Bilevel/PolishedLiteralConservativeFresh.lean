import Bilevel.PolishedLiteralConservativeOracle

/-! The strong literal signal envelope instantiated as an actual measurable
original fresh SFO, with one globally fixed scalar potential per coin. -/
noncomputable section
open MeasureTheory
namespace Bilevel.PolishedLiteral
open PrimitiveGeometry ZeroChainSchedule

/-- A concrete original full-gradient lower SFO exists for the actual source
mean, at B=C_B*mu*beta^2/theta. Measurability, squared integrability, unbiased
centering and global variance are fields of the returned FreshOracle. -/
theorem literal_source_fresh_lower_oracle : ∃ K : ℝ,0<K ∧
    ∀ (X U : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
      [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
      [MeasurableSpace (FullMeanSpace (X:=X) (U:=U))]
      [BorelSpace (FullMeanSpace (X:=X) (U:=U))]
      [SecondCountableTopology (FullMeanSpace (X:=X) (U:=U))]
      (P : Parameters (X:=X) (U:=U)) (θ σ : ℝ),
      1≤θ → 0<P.μ → 0<P.L → 0<P.β → P.β*θ≤1 →
      P.β≤P.radius → P.β≤P.macroNode.width → P.macroNode.width≤P.macroNode.radius →
      P.J=levels θ → P.w=width (1/64) P.β θ →
      let B := K*P.μ*P.β^2/θ
      ∃ hB : 0<B,
      ∃ O : FreshOracle.Oracle (Query:=FullMeanSpace (X:=X) (U:=U))
        (E:=FullMeanSpace (X:=X) (U:=U))
        (BernoulliOracle.law (BernoulliOracle.probability B σ) (BernoulliOracle.probability_le_one hB)) σ,
      O.truth=gradient P.sourceLower ∧
      (∀ coin q,HasGradientAt
        (ChiConservative.samplePotential P.sourceLower P.sourceInactiveLower
          (BernoulliOracle.probability B σ) coin) (O.sample q coin) q) := by
  obtain ⟨K,hK,henv⟩ := literal_source_conservative_envelope
  refine ⟨K,hK,?_⟩
  intro X U _ _ _ _ _ _ _ _ _ P θ σ hθ hμ hL hβ hscale hR hβb hbR hJ hw
  let B := K*P.μ*P.β^2/θ
  have hθ0 : 0<θ := lt_of_lt_of_le zero_lt_one hθ
  have hB : 0<B := by dsimp [B];positivity
  have henv' := henv X U P θ hθ hμ hL hβ hscale hR hβb hbR hJ hw
  have hg : Differentiable ℝ P.sourceLower := P.sourceLower_contDiff.differentiable (by norm_num)
  have hg₀ : Differentiable ℝ P.sourceInactiveLower :=
    (P.inactiveSourceLower_contDiff _ _ (P.w_pos P.J le_rfl)).differentiable (by norm_num)
  have hcg : Continuous (gradient P.sourceLower) :=
    (GradientJetBounds.gradient_contDiff P.sourceLower_contDiff).continuous
  have hcg₀ : Continuous (gradient P.sourceInactiveLower) :=
    (GradientJetBounds.gradient_contDiff
      (P.inactiveSourceLower_contDiff _ _ (P.w_pos P.J le_rfl))).continuous
  let O := ChiConservative.freshOracle P.sourceLower P.sourceInactiveLower hcg hcg₀ (σ:=σ) hB henv'
  refine ⟨hB,O,rfl,?_⟩
  intro coin q
  exact ChiConservative.sample_hasGradientAt P.sourceLower P.sourceInactiveLower hg hg₀ _ coin q

end Bilevel.PolishedLiteral
