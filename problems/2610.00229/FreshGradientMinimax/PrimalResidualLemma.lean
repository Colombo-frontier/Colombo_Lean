import FreshGradientMinimax.PrimalStaticOracle

/-! Complete Lemma C.4 and the fixed fresh oracle immediately following it.
The residual concerns actual full and static-prefix gradients at every query. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

theorem primalInteractionScale_sq {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ) :
    primalInteractionScale L ε μ ^ 2 = 4 * μ * primalValueScale L ε := by
  rw [primalInteractionScale_paper hL hε hμ, mul_pow,
    Real.sq_sqrt (mul_nonneg hμ.le (primalValueScale_pos hL hε).le)]
  ring

theorem primalRevealProbability_pos {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ) (σ : ℝ) :
    0 < primalRevealProbability L ε μ σ :=
  revealProbability_pos (sq_pos_of_pos (mul_pos (by norm_num) (primalInteractionScale_pos hL hε hμ))) (sq_nonneg σ)

theorem primalRevealProbability_le_one (L ε μ σ : ℝ) : primalRevealProbability L ε μ σ ≤ 1 :=
  revealProbability_le_one _ _

theorem primalRevealProbability_zero (L ε μ : ℝ) : primalRevealProbability L ε μ 0 = 1 := by
  simp [primalRevealProbability, revealProbability]

theorem primalRevealProbability_nonzero (L ε μ : ℝ) {σ : ℝ} (hσ : σ ≠ 0) :
    primalRevealProbability L ε μ σ = min 1 ((10 ^ 4) ^ 2 * primalInteractionScale L ε μ ^ 2 / σ ^ 2) := by
  simp only [primalRevealProbability, revealProbability, if_neg (pow_ne_zero 2 hσ), mul_pow]

theorem primalFreshOracle_variance {n dx dy : ℕ}
    (U : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dx) (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hm : μ ≤ L / (4 * primalScalingConstant)) (σ : ℝ) (z : Joint dx dy) :
    (∫ w, jointNormSq (w - (paperCompressedModel U V hL hε hμ hm).jointGradient z)
      ∂(primalFreshOracle U V hL hε hμ hm σ).kernel z) =
      ((primalRevealProbability L ε μ σ)⁻¹ - 1) * jointNormSq
        ((paperCompressedModel U V hL hε hμ hm).jointGradient z - primalStaticBase U V hL hε hμ hm z) :=
  maskedGradientKernel_variance (primalRevealProbability_pos hL hε hμ σ)
    (primalRevealProbability_le_one L ε μ σ) _ _
    (primalStaticBase_measurable U V hL hε hμ hm)
    (paperCompressedModel U V hL hε hμ hm).jointGradient_continuous.measurable z

theorem lemma_C4 {n dx dy : ℕ}
    (U : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dx) (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hm : μ ≤ L / (4 * primalScalingConstant)) (σ : ℝ) :
    let O := paperCompressedModel U V hL hε hμ hm
    let base := primalStaticBase U V hL hε hμ hm
    let p := primalRevealProbability L ε μ σ
    (∀ z, Real.sqrt (jointNormSq (O.jointGradient z - base z)) ≤ 10 ^ 4 * primalInteractionScale L ε μ) ∧
    Measurable base ∧ 0 < p ∧ p ≤ 1 ∧
    (σ = 0 → p = 1) ∧
    (σ ≠ 0 → p = min 1 ((10 ^ 4) ^ 2 * primalInteractionScale L ε μ ^ 2 / σ ^ 2)) ∧
    ∃ K : FreshOracle O σ,
      K.kernel = maskedGradientKernel p base O.jointGradient
        (primalStaticBase_measurable U V hL hε hμ hm) O.jointGradient_continuous.measurable ∧
      (∀ z, (∫ w, w ∂K.kernel z) = O.jointGradient z) ∧
      (∀ z, (∫ w, jointNormSq (w - O.jointGradient z) ∂K.kernel z) =
        (p⁻¹ - 1) * jointNormSq (O.jointGradient z - base z)) ∧
      (∀ z, (∫ w, jointNormSq (w - O.jointGradient z) ∂K.kernel z) ≤ σ ^ 2) := by
  refine ⟨primalStaticBase_residual_norm U V hL hε hμ hm,
    primalStaticBase_measurable U V hL hε hμ hm,
    primalRevealProbability_pos hL hε hμ σ, primalRevealProbability_le_one L ε μ σ,
    ?_, primalRevealProbability_nonzero L ε μ,
    primalFreshOracle U V hL hε hμ hm σ, rfl,
    (primalFreshOracle U V hL hε hμ hm σ).mean,
    primalFreshOracle_variance U V hL hε hμ hm σ,
    (primalFreshOracle U V hL hε hμ hm σ).variance_le⟩
  intro hσ
  subst σ
  exact primalRevealProbability_zero L ε μ

end FreshGradientMinimax
