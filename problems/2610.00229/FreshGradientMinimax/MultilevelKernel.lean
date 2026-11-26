import FreshGradientMinimax.FiniteMixture
import FreshGradientMinimax.IndependentCorrection
import FreshGradientMinimax.GradientDescent

/-! The finite, independently sampled multilevel estimator of F.1.
Its expectation telescopes under the actual mixture law. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {Q : Type*} [MeasurableSpace Q] {d : ℕ}

def multilevelKernel (L : ℕ → Kernel Q (Euclid d)) (K : ℕ) : Kernel Q (Euclid d) :=
  if K = 0 then L 0 else
    finiteMixtureKernel (levelProbability K)
      (fun j => independentCorrectionKernel (L 0) (L (j + 1)) (L j) (levelProbability K j)) K

instance multilevelKernel_markov (L : ℕ → Kernel Q (Euclid d)) [∀ j, IsMarkovKernel (L j)] (K : ℕ) :
    IsMarkovKernel (multilevelKernel L K) := by
  by_cases hK : K = 0
  · simp only [multilevelKernel, if_pos hK]; infer_instance
  · rw [multilevelKernel, if_neg hK]
    exact finiteMixtureKernel_markov _ _ _
      (fun j _ => (level_probability_pos (Nat.pos_of_ne_zero hK) j).le)
      (level_probabilities_sum (Nat.pos_of_ne_zero hK))

variable (L : ℕ → Kernel Q (Euclid d)) [∀ j, IsMarkovKernel (L j)] (K : ℕ) (q : Q)

theorem multilevelKernel_integrable (hi : ∀ j ≤ K, Integrable id (L j q)) :
    Integrable id (multilevelKernel L K q) := by
  by_cases hK : K = 0
  · simpa only [multilevelKernel, hK, if_pos rfl] using hi 0 (Nat.zero_le K)
  · rw [multilevelKernel, if_neg hK]
    apply finiteMixtureKernel_integrable
    intro j hj
    exact independentCorrectionKernel_integrable _ _ _ _ _ (hi 0 (Nat.zero_le K))
      (hi (j + 1) (Nat.succ_le_of_lt hj)) (hi j (Nat.le_of_lt hj))

theorem multilevelKernel_mean (hi : ∀ j ≤ K, Integrable id (L j q)) :
    (∫ r, r ∂multilevelKernel L K q) = ∫ r, r ∂L K q := by
  by_cases hK : K = 0
  · simp [multilevelKernel, hK]
  · have hKpos := Nat.pos_of_ne_zero hK
    rw [multilevelKernel, if_neg hK]
    rw [finiteMixtureKernel_integral (levelProbability K)
      (fun j => independentCorrectionKernel (L 0) (L (j + 1)) (L j) (levelProbability K j))
      K q (fun r : Euclid d => r) (fun j _ => (level_probability_pos hKpos j).le)
      (fun j hj => independentCorrectionKernel_integrable _ _ _ _ _ (hi 0 (Nat.zero_le K))
        (hi (j + 1) (Nat.succ_le_of_lt hj)) (hi j (Nat.le_of_lt hj)))]
    have hsum : (∑ j ∈ Finset.range K, levelProbability K j •
        (∫ r, r ∂independentCorrectionKernel (L 0) (L (j + 1)) (L j) (levelProbability K j) q)) =
        ∑ j ∈ Finset.range K, levelProbability K j •
          ((∫ r, r ∂L 0 q) + (levelProbability K j)⁻¹ • ((∫ r, r ∂L (j + 1) q) - ∫ r, r ∂L j q)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [independentCorrectionKernel_mean _ _ _ _ _ (hi 0 (Nat.zero_le K))
        (hi (j + 1) (Nat.succ_le_of_lt (Finset.mem_range.mp hj)))
        (hi j (Nat.le_of_lt (Finset.mem_range.mp hj)))]
    rw [hsum]
    simp_rw [smul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_smul, level_probabilities_sum hKpos, one_smul]
    exact multilevel_probability_mean hKpos (fun j => ∫ r, r ∂L j q)

theorem multilevelKernel_square_integrable (g : Euclid d)
    (hi : ∀ j ≤ K, Integrable (fun r => ‖r - g‖ ^ 2) (L j q)) :
    Integrable (fun r => ‖r - g‖ ^ 2) (multilevelKernel L K q) := by
  by_cases hK : K = 0
  · simpa only [multilevelKernel, hK, if_pos rfl] using hi 0 (Nat.zero_le K)
  · rw [multilevelKernel, if_neg hK]
    apply finiteMixtureKernel_integrable
    intro j hj
    exact independentCorrectionKernel_square_integrable _ _ _ _ _ g (hi 0 (Nat.zero_le K))
      (hi (j + 1) (Nat.succ_le_of_lt hj)) (hi j (Nat.le_of_lt hj))

theorem multilevelKernel_error (g : Euclid d) {A : ℝ} (hA : 0 ≤ A)
    (hi : ∀ j ≤ K, Integrable (fun r => ‖r - g‖ ^ 2) (L j q))
    (hb : ∀ j ≤ K, (∫ r, ‖r - g‖ ^ 2 ∂L j q) ≤ (1 / 2 : ℝ) ^ j * A) :
    (∫ r, ‖r - g‖ ^ 2 ∂multilevelKernel L K q) ≤ 14 * (K + 1 : ℝ) * A := by
  by_cases hK : K = 0
  · rw [multilevelKernel, if_pos hK]
    simp only [hK, Nat.cast_zero, zero_add, mul_one]
    have h := hb 0 (Nat.zero_le K)
    simp only [pow_zero, one_mul] at h
    linarith
  · have hKpos := Nat.pos_of_ne_zero hK
    have hweighted (j : ℕ) (hj : j < K) :
        levelProbability K j * (∫ r, ‖r - g‖ ^ 2
          ∂independentCorrectionKernel (L 0) (L (j + 1)) (L j) (levelProbability K j) q) ≤
          2 * levelProbability K j * A + 12 * A := by
      have h0 := hb 0 (Nat.zero_le K)
      simp only [pow_zero, one_mul] at h0
      have h1 := hb (j + 1) (Nat.succ_le_of_lt hj)
      have h2 := hb j (Nat.le_of_lt hj)
      have he := independentCorrectionKernel_error (L 0) (L (j + 1)) (L j)
        (levelProbability K j) q g (hi 0 (Nat.zero_le K))
        (hi (j + 1) (Nat.succ_le_of_lt hj)) (hi j (Nat.le_of_lt hj))
      have hp := level_probability_pos hKpos j
      have he' : (∫ r, ‖r - g‖ ^ 2
          ∂independentCorrectionKernel (L 0) (L (j + 1)) (L j) (levelProbability K j) q) ≤
          2 * A + 12 * (levelProbability K j)⁻¹ ^ 2 * (1 / 2 : ℝ) ^ (j + 1) * A := by
        have h12 := mul_le_mul_of_nonneg_left (add_le_add h1 h2)
          (by positivity : 0 ≤ 4 * (levelProbability K j)⁻¹ ^ 2)
        have heq : 4 * (levelProbability K j)⁻¹ ^ 2 *
            ((1 / 2 : ℝ) ^ (j + 1) * A + (1 / 2 : ℝ) ^ j * A) =
            12 * (levelProbability K j)⁻¹ ^ 2 * (1 / 2 : ℝ) ^ (j + 1) * A := by
          rw [pow_succ]; ring
        rw [heq] at h12
        linarith
      have hc : levelProbability K j * (levelProbability K j)⁻¹ ^ 2 *
          (1 / 2 : ℝ) ^ (j + 1) = 1 - (1 / 2 : ℝ) ^ K := by
        have hpform : (1 / 2 : ℝ) ^ (j + 1) = levelProbability K j * (1 - (1 / 2 : ℝ) ^ K) := by
          rw [levelProbability, div_mul_cancel₀ _ (ne_of_gt (level_normalizer_pos hKpos))]
        rw [hpform]
        field_simp
        ring
      have he'' := mul_le_mul_of_nonneg_left he' hp.le
      have hexpand : levelProbability K j *
          (2 * A + 12 * (levelProbability K j)⁻¹ ^ 2 * (1 / 2 : ℝ) ^ (j + 1) * A) =
          2 * levelProbability K j * A + 12 * (1 - (1 / 2 : ℝ) ^ K) * A := by
        calc
          _ = 2 * levelProbability K j * A + 12 *
              (levelProbability K j * (levelProbability K j)⁻¹ ^ 2 * (1 / 2 : ℝ) ^ (j + 1)) * A := by ring
          _ = _ := by rw [hc]
      rw [hexpand] at he''
      nlinarith [mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) K) hA]
    rw [multilevelKernel, if_neg hK]
    rw [finiteMixtureKernel_integral _ _ _ _ _ (fun j _ => (level_probability_pos hKpos j).le)
      (fun j hj => independentCorrectionKernel_square_integrable _ _ _ _ _ g
        (hi 0 (Nat.zero_le K)) (hi (j + 1) (Nat.succ_le_of_lt hj)) (hi j (Nat.le_of_lt hj)))]
    simp only [smul_eq_mul]
    calc
      _ ≤ ∑ j ∈ Finset.range K, (2 * levelProbability K j * A + 12 * A) :=
        Finset.sum_le_sum (fun j hj => hweighted j (Finset.mem_range.mp hj))
      _ = 2 * A + (K : ℝ) * (12 * A) := by
        rw [Finset.sum_add_distrib]
        simp only [← Finset.sum_mul, ← Finset.mul_sum, level_probabilities_sum hKpos,
          Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        ring
      _ ≤ _ := by nlinarith [mul_nonneg (Nat.cast_nonneg K : (0 : ℝ) ≤ K) hA]

theorem multilevelKernel_bias (g : Euclid d) {A : ℝ}
    (hi : ∀ j ≤ K, Integrable id (L j q))
    (hs : Integrable (fun r => ‖r - g‖ ^ 2) (L K q))
    (hb : (∫ r, ‖r - g‖ ^ 2 ∂L K q) ≤ (1 / 2 : ℝ) ^ K * A) :
    ‖(∫ r, r ∂multilevelKernel L K q) - g‖ ^ 2 ≤ (1 / 2 : ℝ) ^ K * A := by
  rw [multilevelKernel_mean L K q hi]
  exact (squared_bias_le_second_moment (fun r => r) g (hi K le_rfl) hs).trans hb

theorem kernel_variance_le_error (M : Kernel Q (Euclid d)) [IsMarkovKernel M]
    (q : Q) (g : Euclid d) (hi : Integrable id (M q))
    (hs : Integrable (fun r => ‖r - g‖ ^ 2) (M q)) :
    (∫ r, ‖r - ∫ z, z ∂M q‖ ^ 2 ∂M q) ≤ ∫ r, ‖r - g‖ ^ 2 ∂M q := by
  have hs0 := square_integrable_of_centered hi g hs
  have hsc := integrable_square_sub_const hi hs0 (∫ z, z ∂M q)
  have hid := second_moment_about_target (fun r : Euclid d => r) (∫ z, z ∂M q) g hi rfl hsc
  linarith [sq_nonneg ‖(∫ z, z ∂M q) - g‖]

end FreshGradientMinimax
