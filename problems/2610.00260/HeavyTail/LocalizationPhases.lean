import HeavyTail.LocalizationSchedule
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.GeomSum

/-! Forward localization phases and their exact reversal into the physical
ceiling schedule. All statements are deterministic. Phase j uses radius R_j
and confidence delta / 2^(J-j); the final radius is R_J. -/
noncomputable section
open scoped BigOperators
namespace HeavyTail

def localizationPhaseRadius (R₀ : ℝ) (j : ℕ) : ℝ := R₀ / (2 : ℝ) ^ j

def localizationPhaseFailure (δ : ℝ) (J j : ℕ) : ℝ := δ / (2 : ℝ) ^ (J - j)

def localizationPhaseLog (δ : ℝ) (J j : ℕ) : ℝ :=
  confidenceLog (localizationPhaseFailure δ J j)

def localizationForwardBudget (G V s μ R₀ q δ C₀ : ℝ) (J j : ℕ) : ℕ :=
  localizationPhaseBudget G V s μ (localizationPhaseRadius R₀ j) q
    (localizationPhaseLog δ J j) C₀

def localizationForwardRawBudget (G V s μ R₀ q δ C₀ : ℝ) (J : ℕ) : ℕ :=
  4 * ∑ j ∈ Finset.range J, localizationForwardBudget G V s μ R₀ q δ C₀ J j

@[simp] theorem localizationPhaseRadius_zero (R₀ : ℝ) :
    localizationPhaseRadius R₀ 0 = R₀ := by simp [localizationPhaseRadius]

theorem localizationPhaseRadius_pos {R₀ : ℝ} (hR₀ : 0 < R₀) (j : ℕ) :
    0 < localizationPhaseRadius R₀ j := by unfold localizationPhaseRadius; positivity

theorem localizationPhaseRadius_succ (R₀ : ℝ) (j : ℕ) :
    localizationPhaseRadius R₀ (j + 1) = localizationPhaseRadius R₀ j / 2 := by
  simp [localizationPhaseRadius, pow_succ, div_div]

theorem localizationPhaseRadius_le_initial {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (j : ℕ) :
    localizationPhaseRadius R₀ j ≤ R₀ := by
  unfold localizationPhaseRadius
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ j)).2
    (le_mul_of_one_le_right hR₀ (one_le_pow₀ (by norm_num)))

theorem localizationPhaseRadius_antitone {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    Antitone (localizationPhaseRadius R₀) := by
  intro j k hjk
  exact div_le_div_of_nonneg_left hR₀ (by positivity : (0 : ℝ) < 2 ^ j)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hjk)

theorem localizationPhaseRadius_terminal (R₀ : ℝ) {J j : ℕ} (hj : j ≤ J) :
    localizationPhaseRadius R₀ j =
      (2 : ℝ) ^ (J - j) * finalLocalizationRadius R₀ J := by
  have hp : (2 : ℝ) ^ J = (2 : ℝ) ^ j * (2 : ℝ) ^ (J - j) := by
    rw [← pow_add, Nat.add_sub_of_le hj]
  unfold localizationPhaseRadius finalLocalizationRadius
  rw [hp]
  field_simp
  <;> ring

theorem localizationPhaseFailure_pos {δ : ℝ} (hδ : 0 < δ) (J j : ℕ) :
    0 < localizationPhaseFailure δ J j := by unfold localizationPhaseFailure; positivity

theorem localizationPhaseFailure_le {δ : ℝ} (hδ : 0 ≤ δ) (J j : ℕ) :
    localizationPhaseFailure δ J j ≤ δ := by
  unfold localizationPhaseFailure
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ (J - j))).2
    (le_mul_of_one_le_right hδ (one_le_pow₀ (by norm_num)))

theorem localizationPhaseFailure_lt_tenth {δ : ℝ} (hδ : 0 ≤ δ)
    (hδ1 : δ < 1 / 10) (J j : ℕ) : localizationPhaseFailure δ J j < 1 / 10 :=
  (localizationPhaseFailure_le hδ J j).trans_lt hδ1

theorem localizationPhaseLog_eq {δ : ℝ} (hδ : 0 < δ) (J j : ℕ) :
    localizationPhaseLog δ J j = confidenceLog δ + (J - j : ℕ) * Real.log 2 := by
  unfold localizationPhaseLog localizationPhaseFailure confidenceLog
  have he : 3 / (δ / (2 : ℝ) ^ (J - j)) = (3 / δ) * (2 : ℝ) ^ (J - j) := by
    field_simp
  rw [he, Real.log_mul (by positivity) (by positivity), Real.log_pow]

theorem localizationPhaseLog_ge_one {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1 / 10)
    (J j : ℕ) : 1 ≤ localizationPhaseLog δ J j :=
  confidenceLog_ge_one (localizationPhaseFailure_pos hδ J j)
    (localizationPhaseFailure_lt_tenth hδ.le hδ1 J j)

theorem localizationPhaseLog_backward {δ : ℝ} (hδ : 0 < δ) {J m : ℕ} (hm : m < J) :
    localizationPhaseLog δ J (J - 1 - m) = stageConfidence (confidenceLog δ) m := by
  rw [localizationPhaseLog_eq hδ]
  have he : J - (J - 1 - m) = m + 1 := by omega
  rw [he]
  rfl

theorem localizationPhaseFailure_sum (δ : ℝ) (J : ℕ) :
    (∑ j ∈ Finset.range J, localizationPhaseFailure δ J j) =
      δ * (1 - (1 / 2 : ℝ) ^ J) := by
  rw [← Finset.sum_range_reflect (localizationPhaseFailure δ J) J]
  calc
    _ = ∑ m ∈ Finset.range J, (δ / 2) * (1 / 2 : ℝ) ^ m := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmJ : m < J := Finset.mem_range.mp hm
      have he : J - (J - 1 - m) = m + 1 := by omega
      unfold localizationPhaseFailure
      rw [he, one_div_pow, pow_succ]
      ring
    _ = (δ / 2) * ∑ m ∈ Finset.range J, (1 / 2 : ℝ) ^ m := (Finset.mul_sum _ _ _).symm
    _ = _ := by rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]; ring

theorem localizationPhaseFailure_sum_le {δ : ℝ} (hδ : 0 ≤ δ) (J : ℕ) :
    (∑ j ∈ Finset.range J, localizationPhaseFailure δ J j) ≤ δ := by
  rw [localizationPhaseFailure_sum]
  nlinarith [mul_nonneg hδ (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) J)]

theorem localizationPhaseFailure_sum_lt {δ : ℝ} (hδ : 0 < δ) (J : ℕ) :
    (∑ j ∈ Finset.range J, localizationPhaseFailure δ J j) < δ := by
  rw [localizationPhaseFailure_sum]
  nlinarith [mul_pos hδ (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) J)]

theorem localizationForwardBudget_backward {δ : ℝ} (hδ : 0 < δ)
    (G V s μ R₀ q C₀ : ℝ) {J m : ℕ} (hm : m < J) :
    localizationForwardBudget G V s μ R₀ q δ C₀ J (J - 1 - m) =
      ⌈localizationBudgetConstant q C₀ *
        physicalStageWeight (G ^ 2 + V) G s μ (finalLocalizationRadius R₀ J)
          (1 / q) (confidenceLog δ) m⌉₊ := by
  unfold localizationForwardBudget
  rw [localizationPhaseLog_backward hδ hm,
    localizationPhaseRadius_terminal R₀ (by omega : J - 1 - m ≤ J)]
  have he : J - (J - 1 - m) = m + 1 := by omega
  rw [he, localizationPhaseBudget_eq_physical]

theorem localizationForwardBudget_sum_eq {δ : ℝ} (hδ : 0 < δ)
    (G V s μ R₀ q C₀ : ℝ) (J : ℕ) :
    (∑ j ∈ Finset.range J, localizationForwardBudget G V s μ R₀ q δ C₀ J j) =
      ∑ m ∈ Finset.range J, ⌈localizationBudgetConstant q C₀ *
        physicalStageWeight (G ^ 2 + V) G s μ (finalLocalizationRadius R₀ J)
          (1 / q) (confidenceLog δ) m⌉₊ := by
  rw [← Finset.sum_range_reflect (localizationForwardBudget G V s μ R₀ q δ C₀ J) J]
  exact Finset.sum_congr rfl fun m hm =>
    localizationForwardBudget_backward hδ G V s μ R₀ q C₀ (Finset.mem_range.mp hm)

theorem localizationForwardRawBudget_eq {δ : ℝ} (hδ : 0 < δ)
    (G V s μ R₀ q C₀ : ℝ) (J : ℕ) :
    (localizationForwardRawBudget G V s μ R₀ q δ C₀ J : ℝ) =
      4 * ∑ m ∈ Finset.range J, (⌈localizationBudgetConstant q C₀ *
        physicalStageWeight (G ^ 2 + V) G s μ (finalLocalizationRadius R₀ J)
          (1 / q) (confidenceLog δ) m⌉₊ : ℝ) := by
  unfold localizationForwardRawBudget
  rw [localizationForwardBudget_sum_eq hδ]
  push_cast
  rfl

theorem localizationForwardBudget_ge_confidence {G V s μ R₀ q δ C₀ : ℝ}
    (hG : 0 ≤ G) (hV : 0 ≤ V) (hs : 0 ≤ s) (hμ : 0 < μ) (hR₀ : 0 < R₀)
    (hq : 0 < q) (hδ : 0 < δ) (hδ1 : δ < 1 / 10) (hC₀ : 0 ≤ C₀)
    (hwarm : R₀ ≤ Real.sqrt 2 * G / μ) (J j : ℕ) :
    localizationPhaseLog δ J j ≤ (localizationForwardBudget G V s μ R₀ q δ C₀ J j : ℝ) := by
  apply localizationPhaseBudget_ge_confidence hG hV hs hμ (localizationPhaseRadius_pos hR₀ j)
    (le_trans zero_le_one (localizationPhaseLog_ge_one hδ hδ1 J j)) hC₀
  exact (localizationPhaseRadius_le_initial hR₀.le j).trans hwarm

theorem localizationForwardBudget_pos {G V s μ R₀ q δ C₀ : ℝ}
    (hG : 0 ≤ G) (hV : 0 ≤ V) (hs : 0 ≤ s) (hμ : 0 < μ) (hR₀ : 0 < R₀)
    (hq : 0 < q) (hδ : 0 < δ) (hδ1 : δ < 1 / 10) (hC₀ : 0 ≤ C₀)
    (hwarm : R₀ ≤ Real.sqrt 2 * G / μ) (J j : ℕ) :
    0 < localizationForwardBudget G V s μ R₀ q δ C₀ J j := by
  apply (Nat.cast_pos (α := ℝ)).mp
  exact lt_of_lt_of_le (zero_lt_one.trans_le (localizationPhaseLog_ge_one hδ hδ1 J j))
    (localizationForwardBudget_ge_confidence hG hV hs hμ hR₀ hq hδ hδ1 hC₀ hwarm J j)

theorem exists_fixedThreshold_forward_schedule (θ : OracleParameters)
    (hμ : 0 < θ.μ) (hT : 0 < θ.T) {τ C₀ R₀ : ℝ}
    (hτ : 0 < τ) (hC₀ : 0 ≤ C₀) (hwarm : R₀ ≤ Real.sqrt 2 * θ.G / θ.μ)
    (hstart : 2 * (localizationTerminalMultiplier (1 - 1 / θ.p)
      (localizationBudgetConstant (1 - 1 / θ.p) C₀) *
      fixedThresholdAmplitude θ.G θ.L θ.s θ.p θ.δ τ θ.T / θ.μ) ≤ R₀) :
    let q := 1 - 1 / θ.p
    let v := fixedThresholdAmplitude θ.G θ.L θ.s θ.p θ.δ τ θ.T
    let M := localizationTerminalMultiplier q (localizationBudgetConstant q C₀)
    ∃ J : ℕ, 1 ≤ J ∧ M * v / θ.μ ≤ finalLocalizationRadius R₀ J ∧
      finalLocalizationRadius R₀ J < 2 * (M * v / θ.μ) ∧
      localizationForwardRawBudget θ.G (θ.L ^ θ.p * τ ^ (2 - θ.p)) θ.s θ.μ
        R₀ q θ.δ C₀ J ≤ θ.T := by
  have hC : 1 ≤ localizationBudgetConstant (1 - 1 / θ.p) C₀ :=
    (by norm_num : (1 : ℝ) ≤ 2).trans (localizationBudgetConstant_bounds hC₀).1
  obtain ⟨J, hJ, hlo, hhi, hbudget⟩ :=
    exists_fixedThreshold_localization_schedule θ hμ hT hτ hC hwarm hstart
  refine ⟨J, hJ, hlo, hhi, ?_⟩
  apply (Nat.cast_le (α := ℝ)).mp
  rw [localizationForwardRawBudget_eq θ.δ_pos]
  exact hbudget

end HeavyTail
