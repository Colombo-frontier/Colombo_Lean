import FreshGradientMinimax.CompressionScaling

/-! Lemma C.3 for the actual function (26), including the floor choice in
(28) and the true gradient of its exactly maximized primal function. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem primal_mu_bound_of_condition {L μ : ℝ} (hμ : 0 < μ)
    (hκ : 4 * primalScalingConstant ≤ L / μ) : μ ≤ L / (4 * primalScalingConstant) := by
  have h := (le_div_iff₀ hμ).mp hκ
  exact (le_div_iff₀ (by norm_num [primalScalingConstant] : 0 < 4 * primalScalingConstant)).mpr
    (by nlinarith only [h])

theorem primal_floor_gap {n : ℕ} {lam Δ : ℝ} (hlam : 0 < lam) (hΔ : 0 ≤ Δ)
    (hn : n + 1 = ⌊Δ / (32 * lam)⌋₊) : 18 * (n + 1 : ℝ) * lam ≤ Δ := by
  have ht : (n + 1 : ℝ) ≤ Δ / (32 * lam) := by
    have h := Nat.floor_le (div_nonneg hΔ (by positivity : 0 ≤ 32 * lam))
    rw [← hn] at h
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have h := (le_div_iff₀ (by positivity : 0 < 32 * lam)).mp ht
  nlinarith only [h, mul_nonneg (by positivity : 0 ≤ (n + 1 : ℝ)) hlam.le]

theorem paperCompressedModel_formula {n dx dy : ℕ} (U : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dx)
    (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy) {L ε μ : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ) (hm : μ ≤ L / (4 * primalScalingConstant))
    (x : Euclid dx) (y : Euclid dy) :
    (paperCompressedModel U V hL hε hμ hm).f x y =
      paperCoreObjective V μ (primalValueScale L ε)
        (compressedCoordinates U (primalLengthScale L ε) (primalCompressionRadius n L ε) x) y +
      (primalValueScale L ε * primalRidgeConstant / (2 * primalLengthScale L ε ^ 2)) * ‖x‖ ^ 2 := by
  change _ + (primalValueScale L ε * primalRidgeConstant / primalLengthScale L ε ^ 2) / 2 * ‖x‖ ^ 2 = _
  ring

theorem lemma_C3 {n dx dy : ℕ} (U : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dx)
    (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy) {L ε μ Δ : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ) (hΔ : 0 ≤ Δ)
    (hκ : 4 * primalScalingConstant ≤ L / μ)
    (hn : n + 1 = ⌊Δ / (32 * primalValueScale L ε)⌋₊) :
    ∃ O : NCObjective dx dy L μ,
      (∀ x y, O.f x y = paperCoreObjective V μ (primalValueScale L ε)
        (compressedCoordinates U (primalLengthScale L ε) (primalCompressionRadius n L ε) x) y +
        (primalValueScale L ε * primalRidgeConstant / (2 * primalLengthScale L ε ^ 2)) * ‖x‖ ^ 2) ∧
      O.DualLocalized 0 ∧ O.PrimalGapAtMost Δ ∧
      (∀ x, O.value x = compressedCoreValue U (primalValueScale L ε) (primalLengthScale L ε)
        (primalCompressionRadius n L ε) (primalRidgeCoefficient L ε) x) ∧
      (∀ x, |compressedCoordinates U (primalLengthScale L ε) (primalCompressionRadius n L ε) x (Fin.last n)| ≤ 1 / 4 →
        2 * ε ≤ ‖gradient O.value x‖) := by
  have hm := primal_mu_bound_of_condition hμ hκ
  refine ⟨paperCompressedModel U V hL hε hμ hm, paperCompressedModel_formula U V hL hε hμ hm,
    paperCompressedModel_localized_zero U V hL hε hμ hm,
    paperCompressedModel_gap U V hL hε hμ hm (primal_floor_gap (primalValueScale_pos hL hε) hΔ hn),
    paperCompressedModel_value U V hL hε hμ hm, ?_⟩
  intro x hx
  rw [NCObjective.true_primal_gradient]
  exact paperCompressedModel_barrier U V hL hε hμ hm x hx

end FreshGradientMinimax
