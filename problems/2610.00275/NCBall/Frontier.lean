import NCBall.MainLower
import NCBall.AlmostSureSamples

/-! # Matching polynomial bounds at two absolute radius conventions

The hard family uses a radius between 37Δ/(800ε) and 37Δ/(400ε).
The uniform upper guarantee uses radius 11Δ/ε. These are explicitly distinct
radius conventions; this theorem does not assert minimax equality at one fixed
radius constant. Both bounds have the same polynomial dependence.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal
namespace NCBall
universe u v

def goldsteinRate (n : ℕ) (L Δ δ ε : ℝ) : ℝ :=
  (n + 1 : ℝ) * L ^ 2 * Δ / (δ * ε ^ 3)

theorem lowerConstant_le_one : lowerConstant ≤ 1 := by
  have h := bumpConstant_pos
  unfold lowerConstant
  apply (div_le_one (by positivity)).2
  linarith

theorem one_le_regimeConstant : 1 ≤ regimeConstant := by
  have h := bumpConstant_pos
  unfold regimeConstant
  linarith

theorem goldsteinRate_ge_one (n : ℕ) {L Δ δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) (hεL : ε ≤ L) (hgap : δ * ε ≤ Δ) :
    1 ≤ goldsteinRate n L Δ δ ε := by
  have hL := hε.trans_le hεL
  have hsq : ε ^ 2 ≤ L ^ 2 := by nlinarith
  have hdim : (1 : ℝ) ≤ n + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hprod := mul_le_mul_of_nonneg_right hsq (mul_pos hδ hε).le
  have hg := mul_le_mul_of_nonneg_left hgap (sq_nonneg L)
  have hd := mul_le_mul_of_nonneg_right hdim (mul_nonneg (sq_nonneg L) (le_trans (by positivity) hgap))
  apply (le_div_iff₀ (mul_pos hδ (pow_pos hε 3))).2
  dsimp [goldsteinRate]
  nlinarith

theorem scalar_budget_at_polynomial_rate {n : ℕ} {L Δ δ ε : ℝ} {N : ℕ}
    (hδ : 0 < δ) (hε : 0 < ε) (hεL : ε ≤ L) (hgap : δ * ε ≤ Δ)
    (hN : (N : ℝ) ≤ 5800 * (1 + goldsteinRate n L Δ δ ε)) :
    (N : ℝ) ≤ 11600 * goldsteinRate n L Δ δ ε := by
  have h := goldsteinRate_ge_one n hδ hε hεL hgap
  linarith

theorem SmoothStochasticClass.toLipschitzSampleModel {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    {μ : Measure Ξ} {f : Space n → ℝ} {F : Ξ → Space n → ℝ} {ℓ : Ξ → ℝ} {R H L Δ : ℝ}
    (hs : SmoothStochasticClass μ f F ℓ R H L Δ) : LipschitzSampleModel μ f F ℓ L := by
  refine ⟨hs.jointly_measurable, hs.sample_integrable, hs.sample_mean,
    hs.modulus_measurable, hs.modulus_nonneg, ?_, hs.modulus_square_integrable, hs.modulus_square_moment⟩
  intro ξ
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.coe_toNNReal _ (hs.modulus_nonneg ξ), Real.dist_eq, dist_eq_norm]
    using hs.sample_lipschitz ξ x y

def GoldsteinHardCertificate (n : ℕ) (ε δ Δ L radius : ℝ) : Prop :=
  (∀ u ∈ goodHiddenFamily n (2 * ε) (ε / δ) Δ,
    SmoothStochasticClass (gaussianRooms n (calibratedDepth (4 * (2 * ε)) (ε / δ) Δ))
      (familyPopulation (2 * ε) (ε / δ) Δ u) (familySample (2 * ε) (ε / δ) Δ L u)
      (sampleLipschitzModulus (4 * (2 * ε)) L) radius (ε / δ) L Δ) ∧
  (∀ (Seed : Type u) [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
    (N : ℕ) (p : CountableRoomPolicy Seed n)
    (out : LinearHistory Seed N → Space n), Measurable out →
    (∀ u ∈ goodHiddenFamily n (2 * ε) (ε / δ) Δ,
      (1 / 2 : ℝ≥0∞) ≤
        (ν.prod (Measure.infinitePi
          (fun _ : ℕ => gaussianRooms n (calibratedDepth (4 * (2 * ε)) (ε / δ) Δ))))
        {rz | clarkeGoldsteinResidual (familyPopulation (2 * ε) (ε / δ) Δ u) δ
          (out (sampleTranscript p.point p.handle (familySample (2 * ε) (ε / δ) Δ L) N (u, rz))) ≤ ε}) →
    lowerConstant * goldsteinRate n L Δ δ ε ≤ N)

theorem bounded_domain_polynomial_frontier {n : ℕ} {ε δ Δ L : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hΔ : 0 ≤ Δ) (hL : 0 < L)
    (hsmall : ε ≤ lowerConstant * L)
    (hlarge : regimeConstant * δ * ε ≤ Δ)
    (hd : regimeConstant * Real.log (2 + Δ * L ^ 2 / (δ * ε ^ 3)) ≤ (n : ℝ) + 1) :
    ∃ (rLower rUpper : ℝ) (c : UpperConfig) (ρ : ℝ) (hρ : 0 < ρ),
      0 < rLower ∧ (37 / 800) * (Δ / ε) ≤ rLower ∧ rLower ≤ (37 / 400) * (Δ / ε) ∧
      rUpper = 11 * Δ / ε ∧ 0 < rUpper ∧
      GoldsteinHardCertificate.{u} n ε δ Δ L rLower ∧
      (2 * (c.K * c.m) : ℕ) ≤ 11600 * goldsteinRate n L Δ δ ε ∧
      (∀ (Ξ : Type v) [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
        (f : CoordSpace (n + 1) → ℝ) (F : Ξ → CoordSpace (n + 1) → ℝ) (ℓ : Ξ → ℝ),
        AELipschitzSampleModel μ f F ℓ L → ∀ x₀ : CoordSpace (n + 1),
        (∀ x ∈ closedBall x₀ rUpper, f x₀ - f x ≤ Δ) →
        ∃ (s : Set Ξ) (hs : MeasurableSet s) (hfull : ∀ᵐ ξ ∂μ, ξ ∈ s),
          letI := full_sample_law_probability μ hs hfull
          MeasurePreserving (Subtype.val : s → Ξ) (μ.comap Subtype.val) μ ∧
          ZerothGuarantee (μ.comap Subtype.val) f (fun ξ : s => F ξ.val)
            x₀ δ ε rUpper ρ hρ c) := by
  have hεL : ε ≤ L := hsmall.trans (by simpa using mul_le_mul_of_nonneg_right lowerConstant_le_one hL.le)
  have hreg : δ * ε ≤ regimeConstant * δ * ε := by
    simpa only [one_mul, mul_assoc] using
      mul_le_mul_of_nonneg_right one_le_regimeConstant (mul_pos hδ hε).le
  have hgap : δ * ε ≤ Δ := hreg.trans hlarge
  have hΔpos : 0 < Δ := (mul_pos hδ hε).trans_le hgap
  have hRpos : 0 < 11 * Δ / ε := by positivity
  obtain ⟨r, hr, hrlo, hrhi, hclass, hhard⟩ :=
    goldstein_main_lower_bound.{u} hε hδ hΔ hL hsmall hlarge hd
  let c := zerothConfig n δ Δ L ε hδ hε hεL
  let ρ := zerothRadius δ Δ L (11 * Δ / ε)
  have hρ : 0 < ρ := zerothRadius_pos hδ hΔ hε hεL hRpos
  refine ⟨r, 11 * Δ / ε, c, ρ, hρ, hr, hrlo, hrhi, rfl, hRpos, ⟨hclass, hhard⟩, ?_, ?_⟩
  · exact scalar_budget_at_polynomial_rate hδ hε hεL hgap
      (zerothConfig_scalar_bound n hδ hΔ hε hεL)
  · intro Ξ _ μ _ f F ℓ hs x₀ hlocal
    exact (ae_zeroth_order_local_success hs hδ hΔ hε hεL hRpos le_rfl x₀ hlocal).2

end NCBall
