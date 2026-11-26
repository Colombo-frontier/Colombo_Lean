import FreshGradientMinimax.LevelAccuracy
import FreshGradientMinimax.MultilevelKernel

/-! Explicit cutoff and relative bias/variance bounds (42)--(43) for
the actual fresh-sample estimator. The known quadratic contributes the
additive vector `a`; no derivative of an unknown minimizer is queried. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

def estimatorCutoff (ρ m e σ : ℝ) : ℕ :=
  if σ = 0 then 0 else max 1 ⌈Real.log (10 * σ ^ 2 / (ρ * m * e)) / Real.log 2⌉₊

def estimatorGamma (ρ : ℝ) (K : ℕ) : ℝ := ρ / (14 * (K + 1 : ℝ))

theorem estimatorGamma_pos {ρ : ℝ} (hρ : 0 < ρ) (K : ℕ) : 0 < estimatorGamma ρ K := by
  unfold estimatorGamma
  positivity

theorem estimatorGamma_le {ρ : ℝ} (hρ : 0 ≤ ρ) (K : ℕ) : estimatorGamma ρ K ≤ ρ := by
  apply (div_le_iff₀ (by positivity : 0 < 14 * (K + 1 : ℝ))).mpr
  nlinarith [mul_nonneg hρ (Nat.cast_nonneg K : (0 : ℝ) ≤ K)]

theorem estimatorGamma_cancel (ρ : ℝ) (K : ℕ) :
    14 * (K + 1 : ℝ) * estimatorGamma ρ K = ρ := by
  unfold estimatorGamma
  field_simp

theorem estimatorCutoff_noise {ρ m e σ : ℝ} (hρ : 0 < ρ) (hm : 0 < m) (he : 0 < e) :
    (1 / 2 : ℝ) ^ estimatorCutoff ρ m e σ * (10 * σ ^ 2) ≤ ρ * m * e := by
  by_cases hσ : σ = 0
  · simp only [hσ, sq, mul_zero, zero_mul]
    positivity
  · let R := 10 * σ ^ 2 / (ρ * m * e)
    have hR : 0 < R := by dsimp [R]; positivity
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hceil : Real.log R / Real.log 2 ≤ (estimatorCutoff ρ m e σ : ℝ) := by
      calc
        _ ≤ (⌈Real.log R / Real.log 2⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ _ := by
          apply Nat.cast_le.mpr
          rw [estimatorCutoff, if_neg hσ]
          exact le_max_right 1 _
    have hlog := (div_le_iff₀ hlog2).mp hceil
    have hpow : R ≤ (2 : ℝ) ^ estimatorCutoff ρ m e σ := by
      apply (Real.log_le_log_iff hR (by positivity)).mp
      simpa only [Real.log_pow] using hlog
    have hnoise := (div_le_iff₀ (mul_pos (mul_pos hρ hm) he)).mp hpow
    have hinv : (1 / 2 : ℝ) ^ estimatorCutoff ρ m e σ =
        ((2 : ℝ) ^ estimatorCutoff ρ m e σ)⁻¹ := by rw [one_div, inv_pow]
    rw [hinv, inv_mul_eq_div]
    exact (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hnoise])

namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

def relativeEstimatorKernel (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (v a : Euclid dy) : Kernel (Euclid dx) (Euclid dy) :=
  multilevelKernel (fun j => S.levelKernel O (2 ^ j)
    (levelSteps ℓ α (estimatorGamma ρ (estimatorCutoff ρ m e σ)) m (2 ^ j)) v a)
    (estimatorCutoff ρ m e σ)

instance relativeEstimatorKernel_markov (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (v a : Euclid dy) : IsMarkovKernel (S.relativeEstimatorKernel O ρ m e v a) := by
  unfold relativeEstimatorKernel
  infer_instance

theorem relativeEstimatorKernel_integrable (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (v a : Euclid dy) (u : Euclid dx) : Integrable id (S.relativeEstimatorKernel O ρ m e v a u) := by
  apply multilevelKernel_integrable
  intro j _
  exact S.levelKernel_integrable O (pow_pos (by norm_num) j) _ v a u

theorem relativeEstimatorKernel_square_integrable (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (v a : Euclid dy) (u : Euclid dx) :
    Integrable (fun r => ‖r - (gradient S.effectiveValue v + a)‖ ^ 2)
      (S.relativeEstimatorKernel O ρ m e v a u) := by
  apply multilevelKernel_square_integrable
  intro j _
  exact S.levelKernel_square_integrable O (pow_pos (by norm_num) j) _ v a u

/-- Equation (42), including the exact zero-noise cutoff. -/
theorem relativeEstimatorKernel_bias (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {ρ m e : ℝ}
    (hρ : 0 < ρ) (hm : 0 < m) (he : 0 < e) (v a : Euclid dy) (u : Euclid dx) :
    ‖(∫ r, r ∂S.relativeEstimatorKernel O ρ m e v a u) - (gradient S.effectiveValue v + a)‖ ^ 2 ≤
      ρ * m * e + ρ * m ^ 2 * ‖u - S.sliceMin v‖ ^ 2 := by
  let K := estimatorCutoff ρ m e σ
  let γ := estimatorGamma ρ K
  have hγ : 0 < γ := estimatorGamma_pos hρ K
  have hb := multilevelKernel_bias
    (fun j => S.levelKernel O (2 ^ j) (levelSteps ℓ α γ m (2 ^ j)) v a)
    K u (gradient S.effectiveValue v + a)
    (fun j _ => S.levelKernel_integrable O (pow_pos (by norm_num) j) _ v a u)
    (S.levelKernel_square_integrable O (pow_pos (by norm_num) K) _ v a u)
    (S.dyadic_level_accuracy O hαℓ hfast hγ hm K v a u)
  have hc := estimatorCutoff_noise (σ := σ) hρ hm he
  have hhalf : (1 / 2 : ℝ) ^ K ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hγle : γ ≤ ρ := estimatorGamma_le hρ.le K
  have hγhalf : (1 / 2 : ℝ) ^ K * γ ≤ ρ :=
    (mul_le_of_le_one_left hγ.le hhalf).trans hγle
  have hd := mul_le_mul_of_nonneg_right hγhalf
    (by positivity : 0 ≤ m ^ 2 * ‖u - S.sliceMin v‖ ^ 2)
  change (1 / 2 : ℝ) ^ K * (10 * σ ^ 2) ≤ ρ * m * e at hc
  change ‖(∫ r, r ∂S.relativeEstimatorKernel O ρ m e v a u) - (gradient S.effectiveValue v + a)‖ ^ 2 ≤ _ at hb
  nlinarith only [hb, hc, hd]

/-- The MSE bound implies (43), with the explicit noise constant 140. -/
theorem relativeEstimatorKernel_error (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {ρ m e : ℝ}
    (hρ : 0 < ρ) (hm : 0 < m) (v a : Euclid dy) (u : Euclid dx) :
    (∫ r, ‖r - (gradient S.effectiveValue v + a)‖ ^ 2 ∂S.relativeEstimatorKernel O ρ m e v a u) ≤
      140 * (estimatorCutoff ρ m e σ + 1 : ℝ) * σ ^ 2 + ρ * m ^ 2 * ‖u - S.sliceMin v‖ ^ 2 := by
  let K := estimatorCutoff ρ m e σ
  let γ := estimatorGamma ρ K
  have hγ : 0 < γ := estimatorGamma_pos hρ K
  have hb := multilevelKernel_error
    (fun j => S.levelKernel O (2 ^ j) (levelSteps ℓ α γ m (2 ^ j)) v a)
    K u (gradient S.effectiveValue v + a)
    (by positivity : 0 ≤ γ * m ^ 2 * ‖u - S.sliceMin v‖ ^ 2 + 10 * σ ^ 2)
    (fun j _ => S.levelKernel_square_integrable O (pow_pos (by norm_num) j) _ v a u)
    (fun j _ => S.dyadic_level_accuracy O hαℓ hfast hγ hm j v a u)
  have hc : 14 * (K + 1 : ℝ) * γ = ρ := estimatorGamma_cancel ρ K
  have heq : 14 * (K + 1 : ℝ) * (γ * m ^ 2 * ‖u - S.sliceMin v‖ ^ 2 + 10 * σ ^ 2) =
      140 * (K + 1 : ℝ) * σ ^ 2 + ρ * m ^ 2 * ‖u - S.sliceMin v‖ ^ 2 := by
    calc
      _ = 140 * (K + 1 : ℝ) * σ ^ 2 + (14 * (K + 1 : ℝ) * γ) * m ^ 2 * ‖u - S.sliceMin v‖ ^ 2 := by ring
      _ = _ := by rw [hc]
  rw [heq] at hb
  exact hb

theorem relativeEstimatorKernel_variance (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {ρ m e : ℝ}
    (hρ : 0 < ρ) (hm : 0 < m) (v a : Euclid dy) (u : Euclid dx) :
    (∫ r, ‖r - ∫ z, z ∂S.relativeEstimatorKernel O ρ m e v a u‖ ^ 2
      ∂S.relativeEstimatorKernel O ρ m e v a u) ≤
      140 * (estimatorCutoff ρ m e σ + 1 : ℝ) * σ ^ 2 + ρ * m ^ 2 * ‖u - S.sliceMin v‖ ^ 2 := by
  exact (kernel_variance_le_error _ _ (gradient S.effectiveValue v + a)
    (S.relativeEstimatorKernel_integrable O ρ m e v a u)
    (S.relativeEstimatorKernel_square_integrable O ρ m e v a u)).trans
    (S.relativeEstimatorKernel_error O hαℓ hfast hρ hm v a u)

end SCObjective
end FreshGradientMinimax
