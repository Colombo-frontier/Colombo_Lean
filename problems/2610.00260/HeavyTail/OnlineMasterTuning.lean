import HeavyTail.OnlineTuning

/-! Exact scalar normalization and tuning of the conservative stage master
numerator. The clipping moment multiplier is arbitrary nonnegative C. -/
noncomputable section
namespace HeavyTail

def onlineMaster (C p M V s R ell n : ℝ) : ℝ :=
  let η := onlineStep p M V s R ell n
  let a := onlineSmoothing R ell
  let β := onlineQuadratic η M R n
  let ε := onlineResidual η M R n
  (R ^ 2 / (2 * a ^ 2) + β * R ^ 2 / 2 +
    n * (η ^ 2 * M ^ 2 / (2 * β) + ε) +
    8 * n * C * (η ^ p * (s * R) ^ p + η ^ 2 * a ^ 2 * (V + M ^ 2)) +
    4 * ell) / (η * n) + M * R / (2 * n)

theorem online_master_algebra {C p η M V s R ell n a β ε : ℝ}
    (hη : 0 < η) (hn : 0 < n) (ha : 0 < a) (hβ : 0 < β) :
    (R ^ 2 / (2 * a ^ 2) + β * R ^ 2 / 2 +
      n * (η ^ 2 * M ^ 2 / (2 * β) + ε) +
      8 * n * C * (η ^ p * (s * R) ^ p + η ^ 2 * a ^ 2 * (V + M ^ 2)) +
      4 * ell) / (η * n) + M * R / (2 * n) =
    (R ^ 2 / (2 * a ^ 2) + 4 * ell) / (η * n) +
      (β * R ^ 2 / 2 + n * (η ^ 2 * M ^ 2 / (2 * β))) / (η * n) +
      ε / η + 8 * C * (η ^ (p - 1) * (s * R) ^ p +
        η * a ^ 2 * (V + M ^ 2)) + M * R / (2 * n) := by
  rw [Real.rpow_sub_one hη.ne' p]
  field_simp
  <;> ring

theorem online_master_normalization {C p M V s R ell n : ℝ} (hM : 0 < M)
    (hV : 0 ≤ V) (hs : 0 < s) (hR : 0 < R) (hell : 1 ≤ ell) (hn : 0 < n) :
    onlineMaster C p M V s R ell n =
      (9 / 2 : ℝ) * (ell / (onlineStep p M V s R ell n * n)) +
      M * R / Real.sqrt n + (5 / 8 : ℝ) * (M * R / n) +
      8 * C * ((onlineStep p M V s R ell n) ^ (p - 1) * (s * R) ^ p +
        onlineStep p M V s R ell n * R ^ 2 * (V + M ^ 2) / ell) := by
  have he : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have hη := onlineStep_pos (p := p) hM hV hs hR he hn
  have ha := onlineSmoothing_bounds hR hell
  have hβ := onlineQuadratic_pos hη hM hR hn
  unfold onlineMaster
  rw [online_master_algebra hη hn ha.1 hβ,
    online_beta_balance hη hM hR hn, online_residual_balance hη hn, ha.2.2]
  field_simp
  <;> ring

theorem online_inverse_sample_rate {M R n : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hn : 1 ≤ n) : M * R / n ≤ M * R / Real.sqrt n := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hs : Real.sqrt n ≤ n := by
    apply (Real.sqrt_le_iff).2
    exact ⟨hn0.le, by nlinarith⟩
  exact div_le_div_of_nonneg_left (mul_nonneg hM hR) (Real.sqrt_pos.2 hn0) hs

theorem online_master_bound {C p M V s R ell n : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (hM : 0 < M) (hV : 0 ≤ V) (hs : 0 < s) (hR : 0 < R)
    (hell : 1 ≤ ell) (hn : 1 ≤ n) :
    onlineMaster C p M V s R ell n ≤
      (96 + 16 * C) * R * ((M + Real.sqrt V) / Real.sqrt n + M * ell / n +
        s * (ell / n) ^ (1 - 1 / p)) := by
  have he : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hη := onlineStep_pos (p := p) hM hV hs hR he hn0
  have hstep := onlineStep_bounds p M V s R ell n
  have hpower := online_power_balance hp hη hs hR he hn0 hstep.2.2
  have htrace := online_trace_balance hM hV hR he hn0 hstep.2.1
  have hinverse := online_inverse_balance (p := p) hM hV hs hR he hn0
  have hrate := mul_le_mul_of_nonneg_left (online_trace_rate hM.le hV hn0) hR.le
  let B := R * ((M + Real.sqrt V) / Real.sqrt n)
  let D := M * R * ell / n
  let H := s * R * (ell / n) ^ (1 - 1 / p)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hU : M * R / Real.sqrt n ≤ B := by
    dsimp [B]
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (show M ≤ M + Real.sqrt V from le_add_of_nonneg_right (Real.sqrt_nonneg V)) hR.le)
      (Real.sqrt_nonneg n)
    convert hh using 1 <;> ring
  have hJ : M * R / n ≤ B := (online_inverse_sample_rate hM.le hR.le hn).trans hU
  have hInv : ell / (onlineStep p M V s R ell n * n) ≤ 16 * D + B + H := by
    calc
      _ ≤ 16 * M * R * ell / n + R * Real.sqrt ((V + M ^ 2) / n) + H := hinverse
      _ ≤ 16 * M * R * ell / n + B + H :=
        add_le_add_right (add_le_add_left hrate _) _
      _ = _ := by dsimp [D]; ring
  have hQ : onlineStep p M V s R ell n * R ^ 2 * (V + M ^ 2) / ell ≤ B :=
    htrace.trans hrate
  have hPQ := mul_le_mul_of_nonneg_left (add_le_add hpower hQ)
    (by positivity : 0 ≤ 8 * C)
  change 8 * C * ((onlineStep p M V s R ell n) ^ (p - 1) * (s * R) ^ p +
    onlineStep p M V s R ell n * R ^ 2 * (V + M ^ 2) / ell) ≤ 8 * C * (H + B) at hPQ
  rw [online_master_normalization hM hV hs hR hell hn0]
  calc
    _ ≤ (9 / 2 : ℝ) * (16 * D + B + H) + B + (5 / 8 : ℝ) * B +
        8 * C * (H + B) := by linarith only [hInv, hU, hJ, hPQ]
    _ ≤ (96 + 16 * C) * (B + D + H) := by
      nlinarith [mul_nonneg hC hB, mul_nonneg hC hD, mul_nonneg hC hH]
    _ = _ := by dsimp [B, D, H]; ring

end HeavyTail
