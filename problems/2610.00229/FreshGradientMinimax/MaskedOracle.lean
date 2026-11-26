import FreshGradientMinimax.Basic

/-! Exact two-point moment calculations for Appendix C, equations (31)--(32).
The finite distribution is represented by its two weights. The global analytic
bound on the full/truncated gradients is an explicit hypothesis, not a theorem
about the paper's hard instance. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def maskedReply (p : ℝ) (base full : E) (reveal : Bool) : E :=
  if reveal then base + p⁻¹ • (full - base) else base

def bernoulliMean (p : ℝ) (f : Bool → E) : E :=
  p • f true + (1 - p) • f false

def bernoulliMSE (p : ℝ) (f : Bool → E) (target : E) : ℝ :=
  p * ‖f true - target‖ ^ 2 + (1 - p) * ‖f false - target‖ ^ 2

theorem masked_unbiased {p : ℝ} (hp : p ≠ 0) (base full : E) :
    bernoulliMean p (maskedReply p base full) = full := by
  simp only [bernoulliMean, maskedReply, Bool.false_eq_true, ↓reduceIte,
    smul_add, smul_smul, mul_inv_cancel₀ hp, one_smul, sub_smul]
  module

theorem masked_true_error (p : ℝ) (base full : E) :
    maskedReply p base full true - full = (p⁻¹ - 1) • (full - base) := by
  simp only [maskedReply, ↓reduceIte]
  module

theorem masked_variance {p : ℝ} (hp : p ≠ 0) (base full : E) :
    bernoulliMSE p (maskedReply p base full) full =
      (p⁻¹ - 1) * ‖full - base‖ ^ 2 := by
  unfold bernoulliMSE
  rw [masked_true_error, norm_smul_sq]
  simp only [maskedReply, Bool.false_eq_true, ↓reduceIte]
  rw [norm_sub_rev base full]
  field_simp
  ring

/-- Noise-free sampling uses p = 1 directly, with no division by the noise level. -/
theorem masked_exact (base full : E) : maskedReply 1 base full true = full := by
  simp [maskedReply]

theorem masked_variance_one (base full : E) :
    bernoulliMSE 1 (maskedReply 1 base full) full = 0 := by
  rw [masked_variance one_ne_zero]
  norm_num

def revealProbability (residualSq noiseSq : ℝ) : ℝ :=
  if noiseSq = 0 then 1 else min 1 (residualSq / noiseSq)

theorem revealProbability_pos {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s) :
    0 < revealProbability r s := by
  unfold revealProbability
  split_ifs with h
  · norm_num
  · exact lt_min (by norm_num) (div_pos hr (lt_of_le_of_ne hs (Ne.symm h)))

theorem revealProbability_le_one (r s : ℝ) : revealProbability r s ≤ 1 := by
  unfold revealProbability
  split_ifs
  · rfl
  · exact min_le_left _ _

theorem masked_variance_budget {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s)
    (base full : E) (hR : ‖full - base‖ ^ 2 ≤ r) :
    bernoulliMSE (revealProbability r s)
      (maskedReply (revealProbability r s) base full) full ≤ s := by
  rw [masked_variance (ne_of_gt (revealProbability_pos hr hs))]
  by_cases hs0 : s = 0
  · simp [revealProbability, hs0]
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    by_cases hrs : 1 ≤ r / s
    · simp [revealProbability, hs0, min_eq_left hrs, hs]
    · have hrs' : r / s ≤ 1 := le_of_not_ge hrs
      rw [revealProbability, if_neg hs0, min_eq_right hrs', inv_div]
      have hrs2 : r ≤ s := (div_le_one hspos).mp hrs'
      have hc : 0 ≤ s / r - 1 := by
        have : 1 ≤ s / r := (le_div_iff₀ hr).mpr (by simpa using hrs2)
        linarith
      calc
        (s / r - 1) * ‖full - base‖ ^ 2 ≤ (s / r - 1) * r :=
          mul_le_mul_of_nonneg_left hR hc
        _ = s - r := by field_simp
        _ ≤ s := by linarith

/-- This theorem bundles the oracle contract that follows from a pointwise residual bound. -/
theorem masked_oracle_contract {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s)
    (base full : E) (hR : ‖full - base‖ ^ 2 ≤ r) :
    0 < revealProbability r s ∧ revealProbability r s ≤ 1 ∧
    bernoulliMean (revealProbability r s)
      (maskedReply (revealProbability r s) base full) = full ∧
    bernoulliMSE (revealProbability r s)
      (maskedReply (revealProbability r s) base full) full ≤ s := by
  exact ⟨revealProbability_pos hr hs, revealProbability_le_one r s,
    masked_unbiased (ne_of_gt (revealProbability_pos hr hs)) base full,
    masked_variance_budget hr hs base full hR⟩

end FreshGradientMinimax
