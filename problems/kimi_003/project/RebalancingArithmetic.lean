import Mathlib

namespace Task006.RebalancingArithmetic

lemma rpow_identity {B L x : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L) (hx : 0 ≤ x) :
    (B ^ (3 / 2 : ℝ) * L ^ (3 / 2 : ℝ) * x ^ (3 / 4 : ℝ)) ^ (2 / 3 : ℝ) =
      B * L * Real.sqrt x := by
  calc
    (B ^ (3 / 2 : ℝ) * L ^ (3 / 2 : ℝ) * x ^ (3 / 4 : ℝ)) ^ (2 / 3 : ℝ) =
        ((B * L) ^ (3 / 2 : ℝ) * x ^ (3 / 4 : ℝ)) ^ (2 / 3 : ℝ) := by
      rw [Real.mul_rpow hB hL]
    _ = ((B * L) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) *
        (x ^ (3 / 4 : ℝ)) ^ (2 / 3 : ℝ) := by
      rw [Real.mul_rpow (Real.rpow_nonneg (mul_nonneg hB hL) _)
        (Real.rpow_nonneg hx _)]
    _ = (B * L) ^ ((3 / 2 : ℝ) * (2 / 3 : ℝ)) *
        x ^ ((3 / 4 : ℝ) * (2 / 3 : ℝ)) := by
      rw [← Real.rpow_mul (mul_nonneg hB hL), ← Real.rpow_mul hx]
    _ = B * L * Real.sqrt x := by
      have h₁ : (3 / 2 : ℝ) * (2 / 3 : ℝ) = 1 := by norm_num
      have h₂ : (3 / 4 : ℝ) * (2 / 3 : ℝ) = 1 / 2 := by norm_num
      rw [h₁, h₂, Real.rpow_one, ← Real.sqrt_eq_rpow]

theorem constants_valid :
    ∀ (C0 d L s : ℝ), 0 ≤ C0 → 0 < d → 0 < L → 1 ≤ s →
      let K0 := (2 * C0) ^ (2 / 3 : ℝ)
      let B := 512 * (1 + K0)
      let C2 := B ^ (3 / 2 : ℝ)
      0 < B ∧ 0 < C2 ∧
      K0 * L / Real.sqrt d ≤ (B / 2) * L * Real.sqrt (s / d) ∧
      Real.exp 128 * Real.exp (-(d * ((B / 2) * L * Real.sqrt (s / d)) ^ 2) /
        (128 * L ^ 2)) ≤ Real.exp (-s) ∧
      (C2 * L ^ (3 / 2 : ℝ) * (s / d) ^ (3 / 4 : ℝ)) ^ (2 / 3 : ℝ) =
        B * L * Real.sqrt (s / d) := by
  intro C0 d L s hC0 hd hL hs
  dsimp only
  set K0 : ℝ := (2 * C0) ^ (2 / 3 : ℝ) with hK0
  set B : ℝ := 512 * (1 + K0) with hB
  set C2 : ℝ := B ^ (3 / 2 : ℝ) with hC2
  have hK0_nonneg : 0 ≤ K0 := by
    rw [hK0]
    exact Real.rpow_nonneg (by linarith) _
  have hB_pos : 0 < B := by
    rw [hB]
    nlinarith
  have hB_lower : 512 ≤ B := by
    rw [hB]
    nlinarith
  have hC2_pos : 0 < C2 := by
    rw [hC2]
    exact Real.rpow_pos_of_pos hB_pos _
  refine ⟨hB_pos, hC2_pos, ?_, ?_, ?_⟩
  · have hsqrt_d : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
    have hsqrt_s : 1 ≤ Real.sqrt s := Real.one_le_sqrt.mpr hs
    have hsqrt_div : Real.sqrt (s / d) = Real.sqrt s / Real.sqrt d :=
      Real.sqrt_div (by linarith) d
    rw [hsqrt_div]
    calc
      K0 * L / Real.sqrt d ≤ ((B / 2) * L) / Real.sqrt d := by
        apply div_le_div_of_nonneg_right _ hsqrt_d.le
        apply mul_le_mul_of_nonneg_right _ hL.le
        rw [hB]
        nlinarith
      _ ≤ (B / 2) * L * (Real.sqrt s / Real.sqrt d) := by
        calc
          (B / 2) * L / Real.sqrt d =
              ((B / 2) * L) * 1 / Real.sqrt d := by ring
          _ ≤ ((B / 2) * L) * Real.sqrt s / Real.sqrt d := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsqrt_s
                (mul_nonneg (by linarith) hL.le)) hsqrt_d.le
          _ = (B / 2) * L * (Real.sqrt s / Real.sqrt d) := by ring
  · have hs0 : 0 ≤ s := by linarith
    have hsqrt_sq : (Real.sqrt (s / d)) ^ 2 = s / d :=
      Real.sq_sqrt (div_nonneg hs0 hd.le)
    have hnormal :
        d * ((B / 2) * L * Real.sqrt (s / d)) ^ 2 / (128 * L ^ 2) =
          B ^ 2 * s / 512 := by
      rw [show ((B / 2) * L * Real.sqrt (s / d)) ^ 2 =
        ((B / 2) * L) ^ 2 * (Real.sqrt (s / d)) ^ 2 by ring, hsqrt_sq]
      field_simp [hd.ne', hL.ne'] <;> ring
    have hB_sq : 512 * B ≤ B ^ 2 := by
      have hm := mul_le_mul_of_nonneg_right hB_lower hB_pos.le
      simpa [pow_two] using hm
    have hB_sq_lower : 512 * 512 ≤ B ^ 2 := by
      calc
        512 * 512 ≤ 512 * B := by nlinarith
        _ ≤ B ^ 2 := hB_sq
    have hmul : (512 * 512) * s ≤ B ^ 2 * s :=
      mul_le_mul_of_nonneg_right hB_sq_lower hs0
    have hkey : 128 + s ≤ B ^ 2 * s / 512 := by
      nlinarith [hmul]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [neg_div, hnormal]
    linarith
  · rw [hC2]
    exact rpow_identity hB_pos.le hL.le (div_nonneg (by linarith) hd.le)

end Task006.RebalancingArithmetic
