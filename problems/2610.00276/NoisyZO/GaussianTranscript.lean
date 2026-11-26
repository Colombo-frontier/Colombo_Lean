import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import NoisyZO.GaussianKernel

/-!
# Finite adaptive Gaussian transcripts

An algorithmic state `α` is updated measurably after every scalar Gaussian
observation.  The update may keep the full history, the current query, and any
internal random seed.  Data processing and the Gaussian composition-product
identity give a one-step KL inequality; induction then gives the finite-horizon
adaptive transcript bound.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace NoisyZO

variable {α : Type*} [MeasurableSpace α]

/-- Push one Gaussian observation through a measurable algorithmic-state update. -/
noncomputable def gaussianStateStep
    (μ : Measure α) (mean : α → ℝ) (hmean : Measurable mean)
    (update : α × ℝ → α) (_hupdate : Measurable update) : Measure α :=
  (μ ⊗ₘ gaussianOracleKernel mean hmean).map update

/-- One adaptive Gaussian state update satisfies the KL chain-rule upper bound. -/
theorem gaussianStateStep_kl_le
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (mean₁ mean₂ : α → ℝ) (hmean₁ : Measurable mean₁) (hmean₂ : Measurable mean₂)
    (update : α × ℝ → α) (hupdate : Measurable update) :
    InformationTheory.klDiv
        (gaussianStateStep μ mean₁ hmean₁ update hupdate)
        (gaussianStateStep ν mean₂ hmean₂ update hupdate) ≤
      InformationTheory.klDiv μ ν +
        ∫⁻ a, ENNReal.ofReal ((mean₁ a - mean₂ a) ^ 2 / 2) ∂μ := by
  calc
    InformationTheory.klDiv
        (gaussianStateStep μ mean₁ hmean₁ update hupdate)
        (gaussianStateStep ν mean₂ hmean₂ update hupdate) ≤
      InformationTheory.klDiv
        (μ ⊗ₘ gaussianOracleKernel mean₁ hmean₁)
        (ν ⊗ₘ gaussianOracleKernel mean₂ hmean₂) := by
          exact InformationTheory.klDiv_map_le _ _ hupdate
    _ = InformationTheory.klDiv μ ν +
        InformationTheory.klDiv
          (μ ⊗ₘ gaussianOracleKernel mean₁ hmean₁)
          (μ ⊗ₘ gaussianOracleKernel mean₂ hmean₂) :=
      gaussianOracle_compProd_chainRule μ ν mean₁ mean₂ hmean₁ hmean₂
    _ = InformationTheory.klDiv μ ν +
        ∫⁻ a, ENNReal.ofReal ((mean₁ a - mean₂ a) ^ 2 / 2) ∂μ := by
          rw [klDiv_gaussianOracle_compProd_sameBase]

/-- Law of the adaptive state after `n` Gaussian observations. -/
noncomputable def adaptiveGaussianLaw
    (μ₀ : Measure α)
    (mean : ℕ → α → ℝ) (hmean : ∀ n, Measurable (mean n))
    (update : ℕ → α × ℝ → α) (hupdate : ∀ n, Measurable (update n)) :
    ℕ → Measure α
  | 0 => μ₀
  | n + 1 => gaussianStateStep
      (adaptiveGaussianLaw μ₀ mean hmean update hupdate n)
      (mean n) (hmean n) (update n) (hupdate n)

/-- Probability is preserved by every adaptive Gaussian update. -/
theorem adaptiveGaussianLaw_isProbability
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (mean : ℕ → α → ℝ) (hmean : ∀ n, Measurable (mean n))
    (update : ℕ → α × ℝ → α) (hupdate : ∀ n, Measurable (update n))
    (n : ℕ) :
    IsProbabilityMeasure (adaptiveGaussianLaw μ₀ mean hmean update hupdate n) := by
  induction n with
  | zero => simpa [adaptiveGaussianLaw]
  | succ n ih =>
      let _ : IsProbabilityMeasure
          (adaptiveGaussianLaw μ₀ mean hmean update hupdate n) := ih
      simp only [adaptiveGaussianLaw]
      unfold gaussianStateStep
      infer_instance

/-- Finite-horizon adaptive Gaussian transcript KL bound. -/
theorem adaptiveGaussianLaw_kl_le
    (μ₀ ν₀ : Measure α) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure ν₀]
    (mean₁ mean₂ : ℕ → α → ℝ)
    (hmean₁ : ∀ n, Measurable (mean₁ n)) (hmean₂ : ∀ n, Measurable (mean₂ n))
    (update : ℕ → α × ℝ → α) (hupdate : ∀ n, Measurable (update n))
    (T : ℕ) :
    InformationTheory.klDiv
        (adaptiveGaussianLaw μ₀ mean₁ hmean₁ update hupdate T)
        (adaptiveGaussianLaw ν₀ mean₂ hmean₂ update hupdate T) ≤
      InformationTheory.klDiv μ₀ ν₀ +
        ∑ t ∈ Finset.range T,
          ∫⁻ a, ENNReal.ofReal ((mean₁ t a - mean₂ t a) ^ 2 / 2)
            ∂(adaptiveGaussianLaw μ₀ mean₁ hmean₁ update hupdate t) := by
  induction T with
  | zero => simp [adaptiveGaussianLaw]
  | succ T ih =>
      let P : Measure α := adaptiveGaussianLaw μ₀ mean₁ hmean₁ update hupdate T
      let Q : Measure α := adaptiveGaussianLaw ν₀ mean₂ hmean₂ update hupdate T
      let _ : IsProbabilityMeasure P :=
        adaptiveGaussianLaw_isProbability μ₀ mean₁ hmean₁ update hupdate T
      let _ : IsProbabilityMeasure Q :=
        adaptiveGaussianLaw_isProbability ν₀ mean₂ hmean₂ update hupdate T
      have hstep := gaussianStateStep_kl_le P Q
        (mean₁ T) (mean₂ T) (hmean₁ T) (hmean₂ T) (update T) (hupdate T)
      change InformationTheory.klDiv
          (gaussianStateStep P (mean₁ T) (hmean₁ T) (update T) (hupdate T))
          (gaussianStateStep Q (mean₂ T) (hmean₂ T) (update T) (hupdate T)) ≤ _
      calc
        InformationTheory.klDiv
            (gaussianStateStep P (mean₁ T) (hmean₁ T) (update T) (hupdate T))
            (gaussianStateStep Q (mean₂ T) (hmean₂ T) (update T) (hupdate T)) ≤
          InformationTheory.klDiv P Q +
            ∫⁻ a, ENNReal.ofReal ((mean₁ T a - mean₂ T a) ^ 2 / 2) ∂P := hstep
        _ ≤ (InformationTheory.klDiv μ₀ ν₀ +
            ∑ t ∈ Finset.range T,
              ∫⁻ a, ENNReal.ofReal ((mean₁ t a - mean₂ t a) ^ 2 / 2)
                ∂(adaptiveGaussianLaw μ₀ mean₁ hmean₁ update hupdate t)) +
            ∫⁻ a, ENNReal.ofReal ((mean₁ T a - mean₂ T a) ^ 2 / 2) ∂P := by
              simpa only [P, Q] using
                add_le_add ih
                  (le_refl (∫⁻ a, ENNReal.ofReal
                    ((mean₁ T a - mean₂ T a) ^ 2 / 2) ∂P))
        _ = InformationTheory.klDiv μ₀ ν₀ +
            ∑ t ∈ Finset.range (T + 1),
                ∫⁻ a, ENNReal.ofReal ((mean₁ t a - mean₂ t a) ^ 2 / 2)
                ∂(adaptiveGaussianLaw μ₀ mean₁ hmean₁ update hupdate t) := by
              dsimp only [P]
              rw [Finset.sum_range_succ, add_assoc]

/-- The adaptive Gaussian transcript KL divergence is finite when the initial KL divergence is
finite and every conditional squared mean difference is integrable. -/
theorem adaptiveGaussianLaw_kl_ne_top
    (μ₀ ν₀ : Measure α) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure ν₀]
    (mean₁ mean₂ : ℕ → α → ℝ)
    (hmean₁ : ∀ n, Measurable (mean₁ n)) (hmean₂ : ∀ n, Measurable (mean₂ n))
    (update : ℕ → α × ℝ → α) (hupdate : ∀ n, Measurable (update n))
    (hfinite₀ : InformationTheory.klDiv μ₀ ν₀ ≠ ∞)
    (hint : ∀ t, Integrable (fun a ↦ (mean₁ t a - mean₂ t a) ^ 2 / 2)
      (adaptiveGaussianLaw μ₀ mean₁ hmean₁ update hupdate t))
    (T : ℕ) :
    InformationTheory.klDiv
        (adaptiveGaussianLaw μ₀ mean₁ hmean₁ update hupdate T)
        (adaptiveGaussianLaw ν₀ mean₂ hmean₂ update hupdate T) ≠ ∞ := by
  have hKL := adaptiveGaussianLaw_kl_le μ₀ ν₀ mean₁ mean₂
    hmean₁ hmean₂ update hupdate T
  apply ne_top_of_le_ne_top _ hKL
  apply ENNReal.add_ne_top.mpr
  refine ⟨hfinite₀, ENNReal.sum_ne_top.mpr ?_⟩
  intro t _ht
  rw [← ofReal_integral_eq_lintegral_ofReal (hint t)
    (ae_of_all _ fun a ↦ by positivity)]
  exact ENNReal.ofReal_ne_top

/-- Real-valued finite transcript bound when all conditional signal costs are integrable. -/
theorem adaptiveGaussianLaw_kl_toReal_le
    (μ₀ ν₀ : Measure α) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure ν₀]
    (mean₁ mean₂ : ℕ → α → ℝ)
    (hmean₁ : ∀ n, Measurable (mean₁ n)) (hmean₂ : ∀ n, Measurable (mean₂ n))
    (update : ℕ → α × ℝ → α) (hupdate : ∀ n, Measurable (update n))
    (hfinite₀ : InformationTheory.klDiv μ₀ ν₀ ≠ ∞)
    (hint : ∀ t, Integrable (fun a ↦ (mean₁ t a - mean₂ t a) ^ 2 / 2)
      (adaptiveGaussianLaw μ₀ mean₁ hmean₁ update hupdate t))
    (T : ℕ) :
    (InformationTheory.klDiv
        (adaptiveGaussianLaw μ₀ mean₁ hmean₁ update hupdate T)
        (adaptiveGaussianLaw ν₀ mean₂ hmean₂ update hupdate T)).toReal ≤
      (InformationTheory.klDiv μ₀ ν₀).toReal +
        ∑ t ∈ Finset.range T,
          ∫ a, (mean₁ t a - mean₂ t a) ^ 2 / 2
            ∂(adaptiveGaussianLaw μ₀ mean₁ hmean₁ update hupdate t) := by
  have hKL := adaptiveGaussianLaw_kl_le μ₀ ν₀ mean₁ mean₂
    hmean₁ hmean₂ update hupdate T
  let q : ℕ → α → ℝ := fun t a ↦ (mean₁ t a - mean₂ t a) ^ 2 / 2
  let P : ℕ → Measure α := adaptiveGaussianLaw μ₀ mean₁ hmean₁ update hupdate
  have hq_nonneg (t : ℕ) (a : α) : 0 ≤ q t a := by
    dsimp only [q]
    positivity
  have hcost (t : ℕ) :
      (∫⁻ a, ENNReal.ofReal (q t a) ∂P t) = ENNReal.ofReal (∫ a, q t a ∂P t) := by
    symm
    exact ofReal_integral_eq_lintegral_ofReal (hint t)
      (ae_of_all (P t) fun a ↦ hq_nonneg t a)
  have hintegral_nonneg (t : ℕ) : 0 ≤ ∫ a, q t a ∂P t :=
    integral_nonneg fun a ↦ hq_nonneg t a
  have hRHS :
      InformationTheory.klDiv μ₀ ν₀ +
          ∑ t ∈ Finset.range T, ∫⁻ a, ENNReal.ofReal (q t a) ∂P t =
        ENNReal.ofReal ((InformationTheory.klDiv μ₀ ν₀).toReal +
          ∑ t ∈ Finset.range T, ∫ a, q t a ∂P t) := by
    calc
      InformationTheory.klDiv μ₀ ν₀ +
          ∑ t ∈ Finset.range T, ∫⁻ a, ENNReal.ofReal (q t a) ∂P t =
        ENNReal.ofReal (InformationTheory.klDiv μ₀ ν₀).toReal +
          ∑ t ∈ Finset.range T, ENNReal.ofReal (∫ a, q t a ∂P t) := by
            rw [ENNReal.ofReal_toReal hfinite₀]
            simp_rw [hcost]
      _ = ENNReal.ofReal (InformationTheory.klDiv μ₀ ν₀).toReal +
          ENNReal.ofReal (∑ t ∈ Finset.range T, ∫ a, q t a ∂P t) := by
            rw [ENNReal.ofReal_sum_of_nonneg]
            intro t _
            exact hintegral_nonneg t
      _ = ENNReal.ofReal ((InformationTheory.klDiv μ₀ ν₀).toReal +
          ∑ t ∈ Finset.range T, ∫ a, q t a ∂P t) := by
            rw [ENNReal.ofReal_add ENNReal.toReal_nonneg]
            exact Finset.sum_nonneg fun t _ ↦ hintegral_nonneg t
  change InformationTheory.klDiv
      (adaptiveGaussianLaw μ₀ mean₁ hmean₁ update hupdate T)
      (adaptiveGaussianLaw ν₀ mean₂ hmean₂ update hupdate T) ≤
    InformationTheory.klDiv μ₀ ν₀ +
      ∑ t ∈ Finset.range T, ∫⁻ a, ENNReal.ofReal (q t a) ∂P t at hKL
  rw [hRHS] at hKL
  have hmono := ENNReal.toReal_mono ENNReal.ofReal_ne_top hKL
  have hnonneg : 0 ≤ (InformationTheory.klDiv μ₀ ν₀).toReal +
      ∑ t ∈ Finset.range T, ∫ a, q t a ∂P t :=
    add_nonneg ENNReal.toReal_nonneg (Finset.sum_nonneg fun t _ ↦ hintegral_nonneg t)
  simpa only [ENNReal.toReal_ofReal hnonneg, q, P] using hmono

end NoisyZO
