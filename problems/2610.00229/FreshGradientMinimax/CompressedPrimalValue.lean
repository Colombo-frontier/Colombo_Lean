import FreshGradientMinimax.PrimalModel

/-! Exact maximization and the primal gap of the protected model. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace
variable {n dx dy : ℕ} (U : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dx)

def compressedCoreValue (lam r R β : ℝ) (x : Euclid dx) : ℝ :=
  lam * coreChain (compressedCoordinates U r R x) + β / 2 * ‖x‖ ^ 2

def compressedCoreGradient (lam r R β : ℝ) (x : Euclid dx) : Euclid dx :=
  lam • compressedPullback U r R x (gradient coreChain (compressedCoordinates U r R x)) + β • x

theorem compressedCoreValue_hasFDerivAt (lam r β : ℝ) {R : ℝ} (hR : 0 < R) (x : Euclid dx) :
    HasFDerivAt (compressedCoreValue U lam r R β) (innerSL ℝ (compressedCoreGradient U lam r R β x)) x := by
  have hf := ((coreChain_contDiff (m := 1)).differentiable (by norm_num) (compressedCoordinates U r R x)).hasGradientAt.hasFDerivAt
  have hd := ((hf.comp x (compressedCoordinates_hasFDerivAt U r hR x)).const_mul lam).add
    (half_quadratic_hasFDerivAt β x)
  apply hd.congr_fderiv
  ext v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    InnerProductSpace.toDual_apply, innerSL_apply, compressedCoreGradient, inner_add_left,
    real_inner_smul_left, compressedPullback_inner, smul_eq_mul]

theorem compressedCoreValue_gradient (lam r β : ℝ) {R : ℝ} (hR : 0 < R) (x : Euclid dx) :
    gradient (compressedCoreValue U lam r R β) x = compressedCoreGradient U lam r R β x :=
  (hasGradientAt_iff_hasFDerivAt.mpr (compressedCoreValue_hasFDerivAt U lam r β hR x)).gradient

theorem compressedCore_exact_max (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ lam : ℝ} (hμ : 0 < μ) (hlam : 0 < lam) (r R β : ℝ) (x : Euclid dx) :
    IsGreatest (Set.range (compressedObjective U (paperCoreObjective V μ lam) r R β x))
      (compressedCoreValue U lam r R β x) := by
  obtain ⟨⟨y, hy⟩, hub⟩ := core_C2_exact_max V hμ hlam (compressedCoordinates U r R x)
  refine ⟨⟨y, ?_⟩, ?_⟩
  · exact congrArg (fun q => q + β / 2 * ‖x‖ ^ 2) hy
  · rintro z ⟨y, rfl⟩
    exact add_le_add_right (hub ⟨y, rfl⟩) _

theorem paperCompressedModel_value (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy) {L ε μ : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ) (hm : μ ≤ L / (4 * primalScalingConstant)) (x : Euclid dx) :
    (paperCompressedModel U V hL hε hμ hm).value x =
      compressedCoreValue U (primalValueScale L ε) (primalLengthScale L ε)
        (primalCompressionRadius n L ε) (primalRidgeCoefficient L ε) x :=
  (compressedCore_exact_max U V hμ (primalValueScale_pos hL hε) _ _ _ x).csSup_eq

theorem paperCompressedModel_primalGradient (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy) {L ε μ : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ) (hm : μ ≤ L / (4 * primalScalingConstant)) (x : Euclid dx) :
    (paperCompressedModel U V hL hε hμ hm).primalGradient x =
      compressedCoreGradient U (primalValueScale L ε) (primalLengthScale L ε)
        (primalCompressionRadius n L ε) (primalRidgeCoefficient L ε) x := by
  rw [← NCObjective.true_primal_gradient,
    show (paperCompressedModel U V hL hε hμ hm).value = compressedCoreValue U (primalValueScale L ε)
      (primalLengthScale L ε) (primalCompressionRadius n L ε) (primalRidgeCoefficient L ε) from
      funext (paperCompressedModel_value U V hL hε hμ hm)]
  exact compressedCoreValue_gradient U _ _ _ (primalCompressionRadius_pos n hL hε) x

theorem compressedCoreValue_gap {lam β : ℝ} (hlam : 0 ≤ lam) (hβ : 0 ≤ β) (r R : ℝ) (x : Euclid dx) :
    compressedCoreValue U lam r R β 0 - compressedCoreValue U lam r R β x ≤ 18 * (n + 1 : ℝ) * lam := by
  have h0 : |coreChain (0 : Euclid (n + 1))| ≤ 9 * (n + 1 : ℝ) := squareLinkCore_bound _
  have hx : |coreChain (compressedCoordinates U r R x)| ≤ 9 * (n + 1 : ℝ) := squareLinkCore_bound _
  have h1 := mul_le_mul_of_nonneg_left (abs_le.mp h0).2 hlam
  have h2 := mul_le_mul_of_nonneg_left (abs_le.mp hx).1 hlam
  simp only [compressedCoreValue, compressedCoordinates_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero]
  nlinarith only [h1, h2, mul_nonneg hβ (sq_nonneg ‖x‖)]

theorem paperCompressedModel_gap (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy) {L ε μ Δ : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ) (hm : μ ≤ L / (4 * primalScalingConstant))
    (hT : 18 * (n + 1 : ℝ) * primalValueScale L ε ≤ Δ) :
    (paperCompressedModel U V hL hε hμ hm).PrimalGapAtMost Δ := by
  intro x
  simp only [paperCompressedModel_value U V hL hε hμ hm]
  exact (compressedCoreValue_gap U (primalValueScale_pos hL hε).le (primalRidgeCoefficient_pos hL hε).le _ _ x).trans hT

end FreshGradientMinimax
