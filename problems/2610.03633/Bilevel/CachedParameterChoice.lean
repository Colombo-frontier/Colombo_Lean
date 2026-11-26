import Bilevel.CachedBudgetCalibration

/-! Concrete positive tolerances for the cached algorithm, including zero
variation and zero upper smoothness. Infinite refresh radius is represented
operationally by disabling refreshes when the anchor smoothness is zero. -/
noncomputable section
namespace Bilevel.CachedParameterChoice

def tilt (E ε : ℝ) : ℝ := if E = 0 then 1 else min 1 (ε/(64*E))

def lowerRadius (Lg E ε : ℝ) : ℝ := ε*tilt E ε/(64*Lg)

def anchorRadius (Lf Lg k E ε : ℝ) : ℝ :=
  if Lf = 0 then lowerRadius Lg E ε else
    min (lowerRadius Lg E ε) (ε/(64*(1+k)*Lf))

def upperRadius (k ε : ℝ) : ℝ := ε/(64*(1+k))

def gradientRadius (E ε : ℝ) : ℝ := ε*tilt E ε/64

theorem tilt_pos {E ε : ℝ} (hE : 0 ≤ E) (hε : 0 < ε) : 0 < tilt E ε := by
  unfold tilt
  split_ifs with h
  · norm_num
  · exact lt_min (by norm_num) (div_pos hε (mul_pos (by norm_num) (lt_of_le_of_ne hE (Ne.symm h))))

theorem tilt_le_one (E ε : ℝ) : tilt E ε ≤ 1 := by
  unfold tilt
  split_ifs
  · rfl
  · exact min_le_left _ _

theorem bias_budget {E ε : ℝ} (hE : 0 ≤ E) (hε : 0 < ε) :
    E*tilt E ε ≤ ε/64 := by
  by_cases h : E = 0
  · simp only [h, zero_mul, mul_zero]; positivity
  · have hEp : 0 < E := lt_of_le_of_ne hE (Ne.symm h)
    have hh := mul_le_mul_of_nonneg_left (min_le_right (1:ℝ) (ε/(64*E))) hE
    unfold tilt
    rw [if_neg h]
    convert hh using 1
    field_simp; ring

theorem lowerRadius_pos {Lg E ε : ℝ} (hLg : 0 < Lg) (hE : 0 ≤ E) (hε : 0 < ε) :
    0 < lowerRadius Lg E ε := by
  unfold lowerRadius
  exact div_pos (mul_pos hε (tilt_pos hE hε)) (by positivity)

theorem lower_budget {Lg E ε : ℝ} (hLg : 0 < Lg) :
    Lg*lowerRadius Lg E ε = ε*tilt E ε/64 := by
  unfold lowerRadius
  field_simp; ring

theorem anchorRadius_pos {Lf Lg k E ε : ℝ}
    (hLf : 0 ≤ Lf) (hLg : 0 < Lg) (hk : 0 ≤ k) (hE : 0 ≤ E) (hε : 0 < ε) :
    0 < anchorRadius Lf Lg k E ε := by
  unfold anchorRadius
  split_ifs with h
  · exact lowerRadius_pos hLg hE hε
  · exact lt_min (lowerRadius_pos hLg hE hε)
      (div_pos hε (mul_pos (by positivity) (lt_of_le_of_ne hLf (Ne.symm h))))

theorem anchorRadius_le_lower (Lf Lg k E ε : ℝ) :
    anchorRadius Lf Lg k E ε ≤ lowerRadius Lg E ε := by
  unfold anchorRadius
  split_ifs
  · rfl
  · exact min_le_left _ _

theorem anchor_budget {Lf Lg k E ε : ℝ} (hLf : 0 ≤ Lf) (hk : 0 ≤ k) (hε : 0 < ε) :
    (1+k)*Lf*anchorRadius Lf Lg k E ε ≤ ε/64 := by
  by_cases h : Lf = 0
  · simp only [h, zero_mul, mul_zero]; positivity
  · have hLf' : 0 < Lf := lt_of_le_of_ne hLf (Ne.symm h)
    have hh := mul_le_mul_of_nonneg_left
      (min_le_right (lowerRadius Lg E ε) (ε/(64*(1+k)*Lf)))
      (by positivity : 0 ≤ (1+k)*Lf)
    unfold anchorRadius
    rw [if_neg h]
    convert hh using 1
    field_simp; ring

theorem upperRadius_pos {k ε : ℝ} (hk : 0 ≤ k) (hε : 0 < ε) : 0 < upperRadius k ε := by
  unfold upperRadius
  positivity

theorem upper_budget {k ε : ℝ} (hk : 0 ≤ k) : (1+k)*upperRadius k ε = ε/64 := by
  unfold upperRadius
  have : 1+k ≠ 0 := by linarith
  field_simp; ring

theorem gradientRadius_pos {E ε : ℝ} (hE : 0 ≤ E) (hε : 0 < ε) :
    0 < gradientRadius E ε := by
  unfold gradientRadius
  exact div_pos (mul_pos hε (tilt_pos hE hε)) (by norm_num)

/-- Scalar inequality behind the all-history confidence choice. -/
def failureTarget (G ε : ℝ) : ℝ := min (1/16) (ε/(16*G))

theorem failureTarget_pos {G ε : ℝ} (hG : 0 < G) (hε : 0 < ε) :
    0 < failureTarget G ε := by unfold failureTarget; positivity

theorem failureTarget_le (G ε : ℝ) : failureTarget G ε ≤ 1/16 := min_le_left _ _

theorem failure_loss_budget {G ε : ℝ} (hG : 0 < G) :
    failureTarget G ε * G ≤ ε/16 := by
  have hh := mul_le_mul_of_nonneg_right (min_le_right (1/16:ℝ) (ε/(16*G))) hG.le
  unfold failureTarget
  convert hh using 1
  field_simp; ring

theorem gradient_cap_pos {Λ Δ ε : ℝ} (hΛ : 0 < Λ) (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    0 < Real.sqrt (2*Λ*Δ) +
      Real.sqrt (CachedBudgetCalibration.outerCount Λ Δ ε * CachedBudgetCalibration.energyCap Λ Δ ε) := by
  have hN : (0:ℝ) < CachedBudgetCalibration.outerCount Λ Δ ε :=
    Nat.cast_pos.mpr (CachedBudgetCalibration.outerCount_pos Λ Δ ε)
  have hcap : 0 < CachedBudgetCalibration.energyCap Λ Δ ε := by
    unfold CachedBudgetCalibration.energyCap
    positivity
  exact add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (Real.sqrt_pos.mpr (mul_pos hN hcap))

theorem confidenceCount_upper {N : ℕ} (hN : 0 < N) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (CachedBudgetCalibration.confidenceCount N δ : ℝ) ≤ 1+8*Real.log (10*N/δ) := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hR : 1 ≤ 10*(N:ℝ)/δ := (le_div_iff₀ hδ).mpr (by linarith)
  have hl : 0 ≤ 8*Real.log (10*(N:ℝ)/δ) := mul_nonneg (by norm_num) (Real.log_nonneg hR)
  have hc := (Nat.ceil_lt_add_one hl).le
  unfold CachedBudgetCalibration.confidenceCount
  rw [Nat.cast_max, Nat.cast_one]
  exact max_le (by linarith) (by linarith)

end Bilevel.CachedParameterChoice

