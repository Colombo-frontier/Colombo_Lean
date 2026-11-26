import SampleReuse.RandomFrameRate

noncomputable section
namespace SampleReuse.RandomFrame

def frameLogConstant (c : ℝ) : ℝ :=
  6 + (Real.log 24 + 2*Real.log (1+2*c))/Real.log 2

theorem frameLogConstant_nonneg {c : ℝ} (hc : 0 < c) : 0 ≤ frameLogConstant c := by
  have hlog := Real.log_nonneg (show 1 ≤ 1+2*c by linarith)
  have h24 := Real.log_nonneg (show (1:ℝ) ≤ 24 by norm_num)
  have h2 := Real.log_pos (show (1:ℝ) < 2 by norm_num)
  unfold frameLogConstant
  positivity

theorem frame_log_envelope {c γ : ℝ} (hc : 0 < c) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    {m N : ℕ} (hm : 0 < m) (hN : N < m) (hupper : (m:ℝ) ≤ 2*c/γ^3) :
    Real.log (24*(m:ℝ)*(N+1)) ≤ frameLogConstant c * Real.log (2/γ) := by
  have hm0 : 0 < (m:ℝ) := by exact_mod_cast hm
  have hN1 : (N:ℝ)+1 ≤ (m:ℝ) := by exact_mod_cast hN
  have hM : 0 < 1+2*c := by linarith
  have hmB : (m:ℝ) ≤ (1+2*c)/γ^3 := hupper.trans
    (div_le_div_of_nonneg_right (by linarith) (pow_nonneg hγ.le 3))
  have hsq : (m:ℝ)^2 ≤ ((1+2*c)/γ^3)^2 :=
    pow_le_pow_left₀ hm0.le hmB 2
  have harg : 24*(m:ℝ)*(N+1) ≤ 24*(1+2*c)^2/γ^6 := by
    calc
      _ ≤ 24*(m:ℝ)^2 := by nlinarith [mul_le_mul_of_nonneg_left hN1 hm0.le]
      _ ≤ 24*((1+2*c)/γ^3)^2 := mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ = _ := by rw [div_pow, ← pow_mul]; ring
  have hlog := Real.log_le_log (show 0 < 24*(m:ℝ)*(N+1) by positivity) harg
  have he : Real.log (24*(1+2*c)^2/γ^6) =
      Real.log 24 + 2*Real.log (1+2*c) - 6*Real.log γ := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_pow, Real.log_pow]
    norm_num
  rw [he] at hlog
  have h2 := Real.log_pos (show (1:ℝ) < 2 by norm_num)
  have hL : Real.log 2 ≤ Real.log (2/γ) := Real.log_le_log (by norm_num)
    ((le_div_iff₀ hγ).mpr (by linarith))
  have hneg : -Real.log γ ≤ Real.log (2/γ) := by
    rw [Real.log_div (by norm_num) hγ.ne']
    linarith
  have hA : 0 ≤ Real.log 24 + 2*Real.log (1+2*c) := by
    have h24 := Real.log_nonneg (show (1:ℝ) ≤ 24 by norm_num)
    have hM1 := Real.log_nonneg (show 1 ≤ 1+2*c by linarith)
    positivity
  have hscale : Real.log 24 + 2*Real.log (1+2*c) ≤
      ((Real.log 24 + 2*Real.log (1+2*c))/Real.log 2) * Real.log (2/γ) := by
    calc
      _ = ((Real.log 24 + 2*Real.log (1+2*c))/Real.log 2)*Real.log 2 :=
        (div_mul_cancel₀ _ h2.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hL (div_nonneg hA h2.le)
  unfold frameLogConstant
  nlinarith

def frameDimensionConstant (P : Parameters) : ℝ :=
  1 + 4*curvatureLengthConstant P +
    32*(curvatureRadiusScale P/curvatureScaleK P)^2*frameLogConstant (curvatureLengthConstant P)

theorem frameDimensionConstant_pos (P : Parameters) : 0 < frameDimensionConstant P := by
  have hc := curvatureLengthConstant_pos P
  have hlog := frameLogConstant_nonneg hc
  unfold frameDimensionConstant
  positivity

/-- A uniform dimension envelope depending only on the fixed model parameters.
It is valid simultaneously for every cap smaller than the selected chain. -/
theorem calibrated_dimension_envelope (P : Parameters) {γ : ℝ}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) {m N : ℕ} (hm : 0 < m) (hN : N < m)
    (hupper : (m:ℝ) ≤ 2*curvatureLengthConstant P/γ^3) :
    (calibratedFrameDimension P γ m N : ℝ) ≤ frameDimensionConstant P *
      (1 + Real.log (2/γ)/γ^4 + 1/γ^3) := by
  let c := curvatureLengthConstant P
  let B := 32*(curvatureRadiusScale P/curvatureScaleK P)^2
  let L := frameLogConstant c
  have hc : 0 < c := curvatureLengthConstant_pos P
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hL : 0 ≤ L := frameLogConstant_nonneg hc
  have hlog := frame_log_envelope hc hγ hγ1 hm hN hupper
  have hcounts : (m:ℝ)+N ≤ 4*c/γ^3 := by
    have hNm : (N:ℝ) ≤ (m:ℝ) := by exact_mod_cast hN.le
    dsimp [c]
    simp only [div_eq_mul_inv] at *
    nlinarith
  have hrough : (calibratedFrameDimension P γ m N : ℝ) ≤
      1 + 4*c/γ^3 + B*L*(Real.log (2/γ)/γ^4) := by
    have hd := (calibrated_dimension_upper P γ hm N).le
    have hl := mul_le_mul_of_nonneg_left hlog (div_nonneg hB (pow_nonneg hγ.le 4))
    dsimp [B, L, c] at *
    simp only [div_eq_mul_inv] at *
    nlinarith
  have hu : 0 ≤ Real.log (2/γ)/γ^4 := div_nonneg
    (Real.log_nonneg ((le_div_iff₀ hγ).mpr (by linarith))) (pow_nonneg hγ.le 4)
  have hv : 0 ≤ 1/γ^3 := by positivity
  have hC : frameDimensionConstant P = 1+4*c+B*L := rfl
  apply hrough.trans
  rw [hC]
  have hu' := mul_nonneg (show 0 ≤ 1+4*c by positivity) hu
  have hv' := mul_nonneg (show 0 ≤ 1+B*L by positivity) hv
  have hc' : 0 ≤ 4*c+B*L := by positivity
  simp only [div_eq_mul_inv] at *
  nlinarith

end SampleReuse.RandomFrame
