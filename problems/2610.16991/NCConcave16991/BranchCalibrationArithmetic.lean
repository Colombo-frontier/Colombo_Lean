import NCConcave16991.DenseSmoothCalibrationArithmetic
import NCConcave16991.GlobalHardPaperProblem
import NCConcave16991.TheoremStatements

/-! # Public floor calibration for the actual Appendix E parameters -/

noncomputable section

namespace NCConcave16991.BranchCalibration

set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

def gapScale : ℝ := 4960000000000000
def diameterScale : ℝ := 160000000000 * Real.sqrt 3

theorem gapScale_pos : 0 < gapScale := by norm_num [gapScale]
theorem diameterScale_pos : 0 < diameterScale := by unfold diameterScale; positivity

def macroCount (A : ℝ) : ℕ := DenseSmoothCalibration.stageCount A 1 gapScale
def chainCount (n : ℕ) (B : ℝ) : ℕ :=
  DenseSmoothCalibration.stageCount B (((n : ℝ) ^ (1 / 4 : ℝ))⁻¹) diameterScale
def chainIndex (n : ℕ) (B : ℝ) : ℕ := chainCount n B - 1

theorem macroCount_bounds {A : ℝ} (hA : 4 * gapScale ≤ A) :
    2 ≤ macroCount A ∧ A / (4 * gapScale) ≤ (macroCount A : ℝ) ∧
      gapScale * (macroCount A : ℝ) ≤ A := by
  have hh := DenseSmoothCalibration.stageCount_bounds gapScale_pos (by norm_num : (0 : ℝ) < 1)
    (by simpa only [mul_one] using hA)
  refine ⟨hh.1,?_,?_⟩
  · simpa only [macroCount,mul_one] using hh.2.1
  · simpa only [macroCount,div_one] using hh.2.2.2

theorem chainCount_bounds {n : ℕ} (hn : 0 < n) {B : ℝ}
    (hB : 4 * diameterScale * (n : ℝ) ^ (1 / 4 : ℝ) ≤ B) :
    2 ≤ chainCount n B ∧ chainIndex n B + 1 = chainCount n B ∧
      B / (4 * diameterScale * (n : ℝ) ^ (1 / 4 : ℝ)) ≤ (chainCount n B : ℝ) ∧
      diameterScale * (n : ℝ) ^ (1 / 4 : ℝ) * (chainIndex n B + 2 : ℕ) ≤ B := by
  let q := (n : ℝ) ^ (1 / 4 : ℝ)
  have hd := diameterScale_pos
  have hq : 0 < q := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hlarge : 4 * diameterScale ≤ B * q⁻¹ := by
    rw [← div_eq_mul_inv]
    exact (le_div_iff₀ hq).mpr hB
  have hh := DenseSmoothCalibration.stageCount_bounds diameterScale_pos (inv_pos.mpr hq) hlarge
  have hS : 2 ≤ chainCount n B := hh.1
  have he : chainIndex n B + 1 = chainCount n B := by unfold chainIndex; omega
  have hl : B / (4 * diameterScale * q) ≤ (chainCount n B : ℝ) := by
    change B / (4 * diameterScale * q) ≤
      (DenseSmoothCalibration.stageCount B q⁻¹ diameterScale : ℝ)
    convert hh.2.1 using 1 <;> ring
  have hu : (chainCount n B : ℝ) ≤ B / (2 * diameterScale * q) := by
    have hnonneg : 0 ≤ B * q⁻¹ / (2 * diameterScale) := by
      have hBp : 0 < B := lt_of_lt_of_le (by positivity) hB
      positivity
    have hf := Nat.floor_le hnonneg
    change (chainCount n B : ℝ) ≤ B * q⁻¹ / (2 * diameterScale) at hf
    convert hf using 1 <;> ring
  refine ⟨hS,he,hl,?_⟩
  have hcast : (chainIndex n B + 2 : ℕ) ≤ 2 * chainCount n B := by omega
  have hcastR : ((chainIndex n B + 2 : ℕ) : ℝ) ≤ 2 * (chainCount n B : ℝ) := by exact_mod_cast hcast
  have hb := (le_div_iff₀ (mul_pos (mul_pos (by norm_num) diameterScale_pos) hq)).mp hu
  have hm := mul_le_mul_of_nonneg_left hcastR (mul_pos diameterScale_pos hq).le
  change diameterScale * q * (chainIndex n B + 2 : ℕ) ≤ B
  nlinarith only [hb,hm]

theorem paperParameters_A (n : ℕ) (hn : 0 < n) (M : ℕ) (hM : 0 < M) (m : ℕ) :
    dimensionlessA (GlobalHardEuclidean.paperParameters n hn M hM m) = gapScale * M := by
  norm_num [dimensionlessA, GlobalHardEuclidean.paperParameters, GlobalHardEuclidean.parameters,gapScale]
  ring

theorem paperParameters_B (n : ℕ) (hn : 0 < n) (M : ℕ) (hM : 0 < M) (m : ℕ) :
    dimensionlessB (GlobalHardEuclidean.paperParameters n hn M hM m) =
      diameterScale * (n : ℝ) ^ (1 / 4 : ℝ) * (m + 2 : ℕ) := by
  simp only [dimensionlessB, GlobalHardEuclidean.paperParameters, GlobalHardEuclidean.parameters,
    GlobalHard.publicDualRadius,diameterScale,Nat.cast_add,Nat.cast_ofNat]
  ring

theorem calibrated_branch_cost {n : ℕ} (hn : 0 < n) {A B c : ℝ} (hc : 0 ≤ c)
    (hA : 4 * gapScale ≤ A)
    (hB : 4 * diameterScale * (n : ℝ) ^ (1 / 4 : ℝ) ≤ B) :
    c / (16 * gapScale * diameterScale) * A * (n : ℝ) ^ (3 / 4 : ℝ) * B ≤
      c * (n : ℝ) * (macroCount A : ℝ) * (chainIndex n B + 1 : ℕ) := by
  have hm := macroCount_bounds hA
  have hs := chainCount_bounds hn hB
  have hd := diameterScale_pos
  have hg := gapScale_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hAp : 0 ≤ A := (mul_pos (by norm_num) gapScale_pos).le.trans hA
  have hBp : 0 ≤ B := (by positivity : 0 < 4 * diameterScale * (n : ℝ) ^ (1 / 4 : ℝ)).le.trans hB
  have hq : 0 < (n : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hp : (n : ℝ) ^ (3 / 4 : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ) = n := by
    rw [← Real.rpow_add (by exact_mod_cast hn)]
    norm_num
  rw [hs.2.1]
  have hh := mul_le_mul hm.2.1 hs.2.2.1 (by positivity) (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hh (mul_nonneg hc (Nat.cast_nonneg n))
  have he : c / (16 * gapScale * diameterScale) * A * (n : ℝ) ^ (3 / 4 : ℝ) * B =
      c * n * (A / (4 * gapScale) * (B / (4 * diameterScale * (n : ℝ) ^ (1 / 4 : ℝ)))) := by
    have hnq : (n : ℝ) / (n : ℝ) ^ (1 / 4 : ℝ) = (n : ℝ) ^ (3 / 4 : ℝ) :=
      (div_eq_iff hq.ne').mpr hp.symm
    rw [← hnq]
    field_simp [gapScale_pos.ne',diameterScale_pos.ne',hq.ne'] <;> ring
  rw [he]
  nlinarith only [hmul]

end NCConcave16991.BranchCalibration
