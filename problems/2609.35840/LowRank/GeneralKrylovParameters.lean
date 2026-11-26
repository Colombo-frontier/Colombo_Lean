import LowRank.GeneralTailEnergyGap
import LowRank.WideKrylovDimensions
import LowRank.PowerBoostedGapArithmetic

/-! Input-independent parameters for every finite Schatten exponent. -/

namespace LowRank
open Matrix
open scoped Matrix
noncomputable section

def powerBoostOrder (p : ℝ) : ℕ := ⌈p / 4⌉₊
def weightedNarrowError (p ε : ℝ) : ℝ := cubicKrylovGap ε / max 1 (p / 2)
def weightedWideError (p : ℝ) (k : ℕ) (ε : ℝ) : ℝ := ε / (max 1 (p / 2) * (k : ℝ))
def generalWideKrylovRank (p : ℝ) (k : ℕ) (ε : ℝ) : ℕ :=
  k + ⌈(4 : ℝ) ^ (p / 2) * ((k : ℝ) * accuracyScale ε)⌉₊

theorem schattenLossFactor_pos (p : ℝ) : 0 < max 1 (p / 2) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem powerBoostOrder_sufficient (p : ℝ) : p / 2 - 1 ≤ ((2 * powerBoostOrder p : ℕ) : ℝ) := by
  have h := Nat.le_ceil (p / 4)
  simp only [powerBoostOrder, Nat.cast_mul, Nat.cast_ofNat]
  linarith

theorem weightedNarrowError_pos {p ε : ℝ} (hε : 0 < ε) : 0 < weightedNarrowError p ε :=
  div_pos (cubicKrylovGap_pos hε) (schattenLossFactor_pos p)

theorem weightedNarrowError_le_one {p ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) : weightedNarrowError p ε ≤ 1 :=
  (div_le_one (schattenLossFactor_pos p)).mpr ((cubicKrylovGap_le_one hε hε1).trans (le_max_left _ _))

theorem weightedWideError_pos {p ε : ℝ} {k : ℕ} (hk : 0 < k) (hε : 0 < ε) :
    0 < weightedWideError p k ε := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  exact div_pos hε (mul_pos (schattenLossFactor_pos p) hkR)

theorem weightedWideError_le_one {p ε : ℝ} {k : ℕ} (hk : 0 < k) (hε1 : ε ≤ 1) :
    weightedWideError p k ε ≤ 1 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hden := one_le_mul_of_one_le_of_one_le (le_max_left 1 (p / 2)) hk1
  exact (div_le_one (by linarith : 0 < max 1 (p / 2) * (k : ℝ))).mpr (hε1.trans hden)

theorem weightedNarrowError_budget {p ε L E : ℝ} {k : ℕ}
    (hε : 0 < ε) (hL : 0 ≤ L)
    (hlarge : (k : ℝ) * accuracyScale ε * L ^ (p / 2) ≤ E) :
    max 1 (p / 2) * (k : ℝ) * (weightedNarrowError p ε / 2) * L ^ (p / 2) ≤ ε * E := by
  have hM := ne_of_gt (schattenLossFactor_pos p)
  have he : max 1 (p / 2) * (k : ℝ) * (weightedNarrowError p ε / 2) =
      (k : ℝ) * cubicKrylovGap ε / 2 := by
    unfold weightedNarrowError
    field_simp
    ring
  rw [he, cubicKrylovGap_eq_mul_scale hε]
  have hn : 0 ≤ ε * ((k : ℝ) * accuracyScale ε * L ^ (p / 2)) := by
    have ha := (accuracyScale_pos hε).le
    positivity
  have hb := mul_le_mul_of_nonneg_left hlarge hε.le
  nlinarith

theorem weightedWideError_budget {p ε L E : ℝ} {k : ℕ}
    (hk : 0 < k) (hε : 0 ≤ ε) (hL : 0 ≤ L) (hE : L ^ (p / 2) ≤ E) :
    max 1 (p / 2) * (k : ℝ) * (weightedWideError p k ε / 2) * L ^ (p / 2) ≤ ε * E := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hM := ne_of_gt (schattenLossFactor_pos p)
  have he : max 1 (p / 2) * (k : ℝ) * (weightedWideError p k ε / 2) = ε / 2 := by
    unfold weightedWideError
    field_simp
    ring
  rw [he]
  exact (mul_le_mul_of_nonneg_right (by linarith : ε / 2 ≤ ε) (Real.rpow_nonneg hL _)).trans
    (mul_le_mul_of_nonneg_left hE hε)

theorem generalWideKrylovRank_ge (p : ℝ) (k : ℕ) (ε : ℝ) : k ≤ generalWideKrylovRank p k ε :=
  Nat.le_add_right _ _

theorem generalWideKrylovRank_surplus (p : ℝ) (k : ℕ) (ε : ℝ) :
    (4 : ℝ) ^ (p / 2) * ((k : ℝ) * accuracyScale ε) ≤ ((generalWideKrylovRank p k ε - k : ℕ) : ℝ) := by
  simp only [generalWideKrylovRank, Nat.add_sub_cancel_left]
  exact Nat.le_ceil _

theorem generalWideKrylovRank_le {p ε : ℝ} {k : ℕ}
    (hk : 0 < k) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (generalWideKrylovRank p k ε : ℝ) ≤ ((4 : ℝ) ^ (p / 2) + 2) * ((k : ℝ) * accuracyScale ε) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ha := accuracyScale_ge_one hε hε1
  have hka : (k : ℝ) ≤ (k : ℝ) * accuracyScale ε := le_mul_of_one_le_right (by positivity) ha
  have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ (4 : ℝ) ^ (p / 2) * ((k : ℝ) * accuracyScale ε))
  simp only [generalWideKrylovRank, Nat.cast_add]
  nlinarith

theorem generalWideKrylovBlockWidth_le {p ε : ℝ} {k : ℕ}
    (hk : 0 < k) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((2 * generalWideKrylovRank p k ε + 2 : ℕ) : ℝ) ≤
      (2 * (4 : ℝ) ^ (p / 2) + 6) * ((k : ℝ) * accuracyScale ε) := by
  have h := generalWideKrylovRank_le (p := p) hk hε hε1
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hka : (1 : ℝ) ≤ (k : ℝ) * accuracyScale ε :=
    one_le_mul_of_one_le_of_one_le hk1 (accuracyScale_ge_one hε hε1)
  push_cast
  nlinarith

end
end LowRank
