import FreshGradientMinimax.RawTruncatedModel
import FreshGradientMinimax.PrimalExterior

/-! A reply outside the protected dual ball that reads only the exposed seed.
It is defined even when the raw coordinate labels collide. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

def rawSeedPotential {n dx : ℕ} (A : Euclid dx →L[ℝ] Euclid (n + 1))
    (lam r R β : ℝ) (j : ℕ) (x : Euclid dx) : ℝ :=
  lam * weightedCoreSeed (coreSeedPrefix n j)
    (linearCompressedCoordinates (primalPrefixRead j A) r R x) + β / 2 * ‖x‖ ^ 2

def rawExteriorReply {n dx dy : ℕ} (A : Euclid dx →L[ℝ] Euclid (n + 1))
    (lam r R β μ : ℝ) (j : ℕ) (z : Joint dx dy) : Joint dx dy :=
  (gradient (rawSeedPotential A lam r R β j) z.1, -(5 * μ) • z.2)

theorem rawSeedPotential_contDiff {n dx : ℕ} (A : Euclid dx →L[ℝ] Euclid (n + 1))
    (lam r R β : ℝ) (j : ℕ) {k : ℕ∞} : ContDiff ℝ k (rawSeedPotential A lam r R β j) :=
  (contDiff_const.mul ((weightedCoreSeed_contDiff _).comp
    (linearCompressedCoordinates_contDiff _ r R))).add (contDiff_const.mul (contDiff_norm_sq ℝ))

theorem rawExteriorReply_continuous {n dx dy : ℕ} (A : Euclid dx →L[ℝ] Euclid (n + 1))
    (lam r R β μ : ℝ) (j : ℕ) : Continuous (rawExteriorReply (dy := dy) A lam r R β μ j) := by
  have hx : Continuous (gradient (rawSeedPotential A lam r R β j)) :=
    (euclid_gradient_contDiff (m := 0) (rawSeedPotential_contDiff A lam r R β j)).continuous
  exact (hx.comp continuous_fst).prodMk (continuous_const.smul continuous_snd)

theorem rawExteriorReply_congr {n dx dy j : ℕ} (A A' : Euclid dx →L[ℝ] Euclid (n + 1))
    (lam r R β μ : ℝ) (h : primalPrefixRead j A = primalPrefixRead j A') :
    rawExteriorReply (dy := dy) A lam r R β μ j = rawExteriorReply A' lam r R β μ j := by
  unfold rawExteriorReply rawSeedPotential
  rw [h]

theorem rawSeedPotential_frame {n dx j : ℕ} (U : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dx)
    (lam r R β : ℝ) (hj : 0 < j) :
    rawSeedPotential (frameCoordinates U) lam r R β j =
      fun x => lam * weightedCoreSeed (coreSeedPrefix n j) (compressedCoordinates U r R x) + β / 2 * ‖x‖ ^ 2 := by
  funext x
  have he : linearCompressedCoordinates (primalPrefixRead j (frameCoordinates U)) r R x =
      corePrimalPrefix j (compressedCoordinates U r R x) := by
    simp only [linearCompressedCoordinates, primalPrefixRead, compressedCoordinates,
      ContinuousLinearMap.comp_apply, map_smul]
  simp only [rawSeedPotential, he, coreSeed_prefix_read hj]

theorem rawSeedPotential_frame_gradient {n dx j : ℕ} (U : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dx)
    (lam r β : ℝ) {R : ℝ} (hR : 0 < R) (hj : 0 < j) (x : Euclid dx) :
    gradient (rawSeedPotential (frameCoordinates U) lam r R β j) x =
      lam • compressedPullback U r R x (weightedCoreSeedGradient (coreSeedPrefix n j) (compressedCoordinates U r R x)) + β • x := by
  rw [rawSeedPotential_frame U lam r R β hj]
  have hs := weightedCoreSeed_hasFDerivAt (coreSeedPrefix n j) (compressedCoordinates U r R x)
  rw [weightedCoreSeedDerivative_eq_inner] at hs
  have hd := ((hs.comp x (compressedCoordinates_hasFDerivAt U r hR x)).const_mul lam).add
    (half_quadratic_hasFDerivAt β x)
  apply HasGradientAt.gradient
  apply hasGradientAt_iff_hasFDerivAt.mpr
  apply hd.congr_fderiv
  ext v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply, InnerProductSpace.toDual_apply, inner_add_left,
    real_inner_smul_left, compressedPullback_inner, smul_eq_mul]

theorem rawExteriorReply_paper {n dx dy j : ℕ} (U : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dx)
    (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy) {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hm : μ ≤ L / (4 * primalScalingConstant)) (hj : 0 < j) (z : Joint dx dy)
    (hy : paperDualProtectionRadius n μ (primalValueScale L ε) ≤ ‖z.2‖) :
    rawExteriorReply (frameCoordinates U) (primalValueScale L ε) (primalLengthScale L ε)
      (primalCompressionRadius n L ε) (primalRidgeCoefficient L ε) μ j z =
      (paperTruncatedModel U V hL hε hμ hm j).jointGradient z := by
  have ht := Real.sqrt_pos.mpr (div_pos (primalValueScale_pos hL hε) hμ)
  have hcap := coreProtectedCapGrad_exterior V hμ ht (coreLinkPrefix n j) (coreLinkPrefix_bound n j)
    (compressedCoordinates U (primalLengthScale L ε) (primalCompressionRadius n L ε) z.1) z.2
    (paperDualProtectionRadius_height hμ (primalValueScale_pos hL hε) z.2 hy)
  have he : μ * Real.sqrt (primalValueScale L ε / μ) ^ 2 = primalValueScale L ε := by
    rw [Real.sq_sqrt (div_nonneg (primalValueScale_pos hL hε).le hμ.le)]
    exact mul_div_cancel₀ _ (ne_of_gt hμ)
  apply Prod.ext
  · change gradient (rawSeedPotential _ _ _ _ _ _) z.1 = compressedGradX U _ _ _ _ z.1 z.2
    rw [rawSeedPotential_frame_gradient U _ _ _ (primalCompressionRadius_pos n hL hε) hj]
    unfold compressedGradX paperTruncatedCore truncatedCoreObjective
    rw [maskedCore_gradient_u V hμ ht]
    simp only [maskedCoreGradU, hcap.1, sub_zero, he, compressedPullback, map_smul, smul_smul]
    congr 1
    rw [mul_comm]
  · change -(5 * μ) • z.2 = gradient (paperTruncatedCore V μ (primalValueScale L ε) j _) z.2
    unfold paperTruncatedCore truncatedCoreObjective
    rw [maskedCore_gradient_y V hμ ht]
    simp only [maskedCoreGradY, hcap.2, ← sub_smul]
    congr 1
    ring

end FreshGradientMinimax
