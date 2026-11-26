import Bilevel.PolishedLiteralConservativeSignal

/-! A globally fixed conservative original lower SFO for the actual literal
mean. Its Bernoulli probability and full-gradient envelope have precisely
the source scale B=C_B*mu*beta^2/theta. -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory
namespace Bilevel.PolishedLiteral
open PrimitiveGeometry ChiBoundedChain ZeroChainSchedule
namespace Parameters
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
variable (P : Parameters (X:=X) (U:=U))

def sourceInactiveLower : FullMeanSpace (X:=X) (U:=U) → ℝ :=
  P.inactiveSourceLower (P.w P.J/8) (P.w P.J)

end Parameters

theorem literal_source_conservative_envelope : ∃ K : ℝ,0<K ∧
    ∀ (X U : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
      [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
      (P : Parameters (X:=X) (U:=U)) (θ : ℝ),
      1≤θ → 0<P.μ → 0<P.L → 0<P.β → P.β*θ≤1 →
      P.β≤P.radius → P.β≤P.macroNode.width → P.macroNode.width≤P.macroNode.radius →
      P.J=levels θ → P.w=width (1/64) P.β θ →
      ∀ q : FullMeanSpace (X:=X) (U:=U),
      ‖gradient P.sourceLower q-gradient P.sourceInactiveLower q‖≤K*P.μ*P.β^2/θ := by
  obtain ⟨B,hB,hb⟩ := signal_residual_c1_bounds
  let K := B^2*(Real.exp 2+1)+2*PolishedLiteralCompensated.C*B*Real.exp 2
  have hK : 0<K := by
    have hN := PolishedLiteralCompensated.C_pos
    dsimp [K]
    positivity
  refine ⟨K,hK,?_⟩
  intro X U _ _ _ _ _ _ P θ hθ hμ hL hβ hscale hR hβb hbR hJ hw q
  let w := P.w P.J
  let δ := w/8
  have hwpos : 0<w := P.w_pos P.J le_rfl
  have hδpos : 0<δ := by dsimp [δ];positivity
  have hδw : δ≤w := by dsimp [δ];linarith
  have hpow : θ^(-bExponent P.J)≤1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hθ (neg_nonpos.mpr (bExponent_nonneg _))
  have hwβ : w≤P.β/64 := by
    dsimp only [w]
    rw [hw]
    unfold width
    have hh := mul_le_mul_of_nonneg_left hpow (show 0≤(1/64:ℝ)*P.β by positivity)
    nlinarith only [hh]
  have hδs : δ≤P.β/16 := by dsimp [δ];linarith
  have hws : w≤Real.exp 2*P.β/θ := by
    have ht := (final_width_bounds (1/64) P.β θ (by norm_num) hβ.le hθ).2
    have hθ0 : 0<θ := lt_of_lt_of_le zero_lt_one hθ
    have hbnd : Real.exp 2*(1/64)*P.β/θ≤Real.exp 2*P.β/θ := by
      have hp : 0≤Real.exp 2*P.β/θ := by positivity
      convert mul_le_mul_of_nonneg_left (by norm_num : (1/64:ℝ)≤1) hp using 1 <;> ring
    dsimp only [w]
    rw [hw,hJ]
    exact ht.trans hbnd
  change ‖gradient P.sourceLower q-gradient (P.inactiveSourceLower δ w) q‖≤_
  rw [P.source_gradient_difference_eq_signal δ w hwpos]
  apply (P.signalFull_gradient_bound δ w hwpos q).trans
  exact P.signalY_scaled_bound δ w θ B hB hμ hL hβ hθ hscale hwpos hws hδpos hδw
    (hb X U P δ hL.le hβ hδpos hδs hR hβb hbR) _

/-- Every scalar sample has the actual returned full gradient, globally
unbiased mean, and globally bounded squared-error variance. Neither a
query-dependent mask nor an adaptive probability is introduced. -/
theorem literal_source_conservative_sfo : ∃ K : ℝ,0<K ∧
    ∀ (X U : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
      [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
      (P : Parameters (X:=X) (U:=U)) (θ σ : ℝ),
      1≤θ → 0<P.μ → 0<P.L → 0<P.β → P.β*θ≤1 →
      P.β≤P.radius → P.β≤P.macroNode.width → P.macroNode.width≤P.macroNode.radius →
      P.J=levels θ → P.w=width (1/64) P.β θ →
      let B := K*P.μ*P.β^2/θ
      ∃ hB : 0<B,
      let p := BernoulliOracle.probability B σ
      (∀ coin q,HasGradientAt (ChiConservative.samplePotential P.sourceLower P.sourceInactiveLower p coin)
        (ChiConservative.sampleGradient P.sourceLower P.sourceInactiveLower p coin q) q) ∧
      (∀ q,(∫ coin,ChiConservative.sampleGradient P.sourceLower P.sourceInactiveLower p coin q
        ∂BernoulliOracle.law p (BernoulliOracle.probability_le_one hB))=gradient P.sourceLower q) ∧
      (∀ q,(∫ coin,‖ChiConservative.sampleGradient P.sourceLower P.sourceInactiveLower p coin q-
        gradient P.sourceLower q‖^2 ∂BernoulliOracle.law p (BernoulliOracle.probability_le_one hB))≤σ^2) := by
  obtain ⟨K,hK,henv⟩ := literal_source_conservative_envelope
  refine ⟨K,hK,?_⟩
  intro X U _ _ _ _ _ _ P θ σ hθ hμ hL hβ hscale hR hβb hbR hJ hw
  let B := K*P.μ*P.β^2/θ
  have hθ0 : 0<θ := lt_of_lt_of_le zero_lt_one hθ
  have hB : 0<B := by dsimp [B];positivity
  have hg : Differentiable ℝ P.sourceLower := P.sourceLower_contDiff.differentiable (by norm_num)
  have hg₀ : Differentiable ℝ P.sourceInactiveLower :=
    (P.inactiveSourceLower_contDiff _ _ (P.w_pos P.J le_rfl)).differentiable (by norm_num)
  have hb := henv X U P θ hθ hμ hL hβ hscale hR hβb hbR hJ hw
  refine ⟨hB,?_,?_,?_⟩
  · exact ChiConservative.sample_hasGradientAt P.sourceLower P.sourceInactiveLower hg hg₀ _
  · exact ChiConservative.sample_mean P.sourceLower P.sourceInactiveLower _
      (BernoulliOracle.probability_pos hB) (BernoulliOracle.probability_le_one hB)
  · exact ChiConservative.sample_variance (σ:=σ) hB hb

end Bilevel.PolishedLiteral
