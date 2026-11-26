import FreshGradientMinimax.PrimalCoinLaw

/-! At the original protection radius, all cap gradients are the same
radial field. The actual oracle therefore uses only the exposed seed. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem coreProtectedWeight_exterior {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u : Euclid (n + 1)) (y : Euclid dy)
    (hy : 4 * coreCapHeight n μ t ≤ μ * ‖y‖ ^ 2) :
    coreProtectedWeight V μ t mask u y = 1 := by
  have hΓ := (abs_le.mp (coreInteraction_height_bound V hμ ht mask hm u y)).1
  have hgap : coreCapHeight n μ t ≤ coreProtectedWall n μ t y - coreProtectedQ V μ t mask u y := by
    unfold coreProtectedWall coreProtectedQ
    nlinarith only [hy, hΓ]
  unfold coreProtectedWeight
  rw [smoothRampSlope_clamp (coreCapHeight_pos n hμ ht)]
  exact min_eq_left (((one_le_div (coreCapHeight_pos n hμ ht)).mpr hgap).trans (le_max_right _ _))

theorem coreProtectedCapGrad_exterior {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u : Euclid (n + 1)) (y : Euclid dy)
    (hy : 4 * coreCapHeight n μ t ≤ μ * ‖y‖ ^ 2) :
    coreProtectedCapGradU V μ t mask u y = 0 ∧ coreProtectedCapGradY V μ t mask u y = (4 * μ) • y := by
  simp only [coreProtectedCapGradU, coreProtectedCapGradY,
    coreProtectedWeight_exterior V hμ ht mask hm u y hy, sub_self, zero_smul, one_smul, zero_add, and_self]

theorem truncatedCore_exterior_gradients_eq {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (k : ℕ) (u : Euclid (n + 1)) (y : Euclid dy)
    (hu : ∀ i : Fin (n + 1), k < i.val → |u i| ≤ 1 / 4)
    (hy : 4 * coreCapHeight n μ t ≤ μ * ‖y‖ ^ 2) :
    gradient (fun v => coreProtectedObjective V μ t v y) u =
      gradient (fun v => truncatedCoreObjective V μ t (k + 1) v y) u ∧
    gradient (coreProtectedObjective V μ t u) y = gradient (truncatedCoreObjective V μ t (k + 1) u) y := by
  have hfull := coreProtectedCapGrad_exterior V hμ ht (fun _ => 1) (by intro i; norm_num) u y hy
  have hpart := coreProtectedCapGrad_exterior V hμ ht (coreLinkPrefix n (k + 1)) (coreLinkPrefix_bound _ _) u y hy
  simp only [coreProtectedObjective_gradient_u V hμ ht, coreProtectedObjective_gradient_y V hμ ht,
    truncatedCoreObjective, maskedCore_gradient_u V hμ ht, maskedCore_gradient_y V hμ ht,
    coreProtectedGradU, coreProtectedGradY, maskedCoreGradU, maskedCoreGradY,
    coreSeed_prefix_gradient u hu, hfull.1, hfull.2, hpart.1, hpart.2, and_self]

def paperDualProtectionRadius (n : ℕ) (μ lam : ℝ) : ℝ :=
  2 * Real.sqrt ((768 * (n + 1 : ℝ) * lam) / μ)

theorem paperDualProtectionRadius_height {n dy : ℕ} {μ lam : ℝ} (hμ : 0 < μ) (hlam : 0 < lam)
    (y : Euclid dy) (hy : paperDualProtectionRadius n μ lam ≤ ‖y‖) :
    4 * coreCapHeight n μ (Real.sqrt (lam / μ)) ≤ μ * ‖y‖ ^ 2 := by
  rw [coreCapHeight_paper n hμ hlam.le]
  have hs := pow_le_pow_left₀ (by unfold paperDualProtectionRadius; positivity :
    0 ≤ paperDualProtectionRadius n μ lam) hy 2
  have he : paperDualProtectionRadius n μ lam ^ 2 = 4 * (768 * (n + 1 : ℝ) * lam) / μ := by
    rw [paperDualProtectionRadius, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  rw [he] at hs
  simpa only [mul_comm] using (div_le_iff₀ hμ).mp hs

theorem paperTruncatedModel_exterior_eq {n dx dy : ℕ}
    (U : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dx) (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hm : μ ≤ L / (4 * primalScalingConstant)) (k : ℕ) (z : Joint dx dy)
    (hu : ∀ i : Fin (n + 1), k < i.val →
      |compressedCoordinates U (primalLengthScale L ε) (primalCompressionRadius n L ε) z.1 i| ≤ 1 / 4)
    (hy : paperDualProtectionRadius n μ (primalValueScale L ε) ≤ ‖z.2‖) :
    (paperCompressedModel U V hL hε hμ hm).jointGradient z =
      (paperTruncatedModel U V hL hε hμ hm (k + 1)).jointGradient z := by
  have h := truncatedCore_exterior_gradients_eq V hμ
    (Real.sqrt_pos.mpr (div_pos (primalValueScale_pos hL hε) hμ)) k _ z.2 hu
    (paperDualProtectionRadius_height hμ (primalValueScale_pos hL hε) z.2 hy)
  apply Prod.ext
  · change compressedGradX U _ _ _ _ z.1 z.2 = compressedGradX U _ _ _ _ z.1 z.2
    unfold compressedGradX paperCoreObjective paperTruncatedCore
    rw [h.1]
  · exact h.2

theorem jointMaskedReply_self {dx dy : ℕ} (p : ℝ) (z : Joint dx dy) (c : Bool) :
    jointMaskedReply p z z c = z := by
  cases c <;> simp [jointMaskedReply, maskedReply]

theorem primalCoinReply_exterior {n dx dy : ℕ}
    (U : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dx) (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hm : μ ≤ L / (4 * primalScalingConstant)) (σ : ℝ) (k : ℕ) (z : Joint dx dy) (c : Bool)
    (hu : ∀ i : Fin (n + 1), k < i.val →
      |compressedCoordinates U (primalLengthScale L ε) (primalCompressionRadius n L ε) z.1 i| ≤ 1 / 4)
    (hy : paperDualProtectionRadius n μ (primalValueScale L ε) ≤ ‖z.2‖) :
    primalCoinReply U V hL hε hμ hm σ c z =
      (paperTruncatedModel U V hL hε hμ hm (k + 1)).jointGradient z := by
  have hbase : primalStaticBase U V hL hε hμ hm z =
      (paperCompressedModel U V hL hε hμ hm).jointGradient z :=
    (paperTruncatedModel_exterior_eq U V hL hε hμ hm (primalStaticIndex U V L ε z).val z
      (primalStaticIndex_hidden U V L ε z).1 hy).symm
  rw [primalCoinReply, hbase, jointMaskedReply_self]
  exact paperTruncatedModel_exterior_eq U V hL hε hμ hm k z hu hy

end FreshGradientMinimax
