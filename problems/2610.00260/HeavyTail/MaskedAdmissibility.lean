import HeavyTail.MaskedCalibration

/-! The tuned one-coordinate revelation oracle satisfies both original moment
constraints at every query, with constants independent of dimension. -/

open MeasureTheory
open scoped InnerProductSpace
namespace HeavyTail.MaskedLower
noncomputable section

theorem masked_scalar_budgets {k : ℕ} (hk : 0 < k) {L s p π a : ℝ}
    (hL : 0 ≤ L) (hs : 0 ≤ s) (hp : 1 ≤ p) (hπ : 0 < π) (hkπ : (k : ℝ) * π ≤ 1)
    (hdim : L ^ 2 ≤ (k : ℝ) * s ^ 2) (ha : 0 ≤ a)
    (hab : a ≤ (L / (4 * Real.sqrt k)) * ((k : ℝ) * π) ^ (1 - 1 / p)) :
    2 * (((k : ℝ) * π) * ((a / Real.sqrt k) / π) ^ p + a ^ p) ≤ L ^ p ∧
    2 * (((k : ℝ) * π) * (((a / Real.sqrt k) / π) * (1 / Real.sqrt k)) ^ p + a ^ p) ≤ s ^ p := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hsqrt : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hkR
  have hsqrt1 : 1 ≤ Real.sqrt (k : ℝ) := Real.one_le_sqrt.mpr
    (by exact_mod_cast (Nat.succ_le_of_lt hk))
  have hr : 0 < (k : ℝ) * π := mul_pos hkR hπ
  have heStrong : (a / Real.sqrt (k : ℝ)) / π =
      (a * Real.sqrt (k : ℝ)) / ((k : ℝ) * π) := by
    calc
      _ = (a * Real.sqrt (k : ℝ)) / ((Real.sqrt (k : ℝ)) ^ 2 * π) := by
        field_simp [hsqrt.ne', hπ.ne']
        <;> simp [Real.sq_sqrt hkR.le, mul_assoc, mul_comm, mul_left_comm]
      _ = _ := by rw [Real.sq_sqrt hkR.le]
  have heWeak : ((a / Real.sqrt (k : ℝ)) / π) * (1 / Real.sqrt (k : ℝ)) =
      a / ((k : ℝ) * π) := by
    calc
      _ = a / ((Real.sqrt (k : ℝ)) ^ 2 * π) := by
        field_simp [hsqrt.ne', hπ.ne']
        <;> simp [Real.sq_sqrt hkR.le, mul_assoc, mul_comm, mul_left_comm]
      _ = _ := by rw [Real.sq_sqrt hkR.le]
  have hscaled : a * Real.sqrt (k : ℝ) ≤ (L / 4) * ((k : ℝ) * π) ^ (1 - 1 / p) := by
    have hm := mul_le_mul_of_nonneg_right hab hsqrt.le
    convert hm using 1 <;> field_simp [hsqrt.ne'] <;> ring
  have hstrong := sparse_power_budget (by positivity : 0 ≤ L / 4) hr hkπ hp
    (mul_nonneg ha hsqrt.le) hscaled
  have hbaseStrong : a ^ p ≤ (L / 4) ^ p :=
    (Real.rpow_le_rpow ha (by nlinarith : a ≤ a * Real.sqrt (k : ℝ)) (by linarith)).trans hstrong.2
  have hweakAmplitude : a ≤ ((L / Real.sqrt k) / 4) * ((k : ℝ) * π) ^ (1 - 1 / p) := by
    rw [div_div, mul_comm (Real.sqrt (k : ℝ)) (4 : ℝ)]
    exact hab
  have hweak := sparse_power_budget (by positivity : 0 ≤ (L / Real.sqrt k) / 4)
    hr hkπ hp ha hweakAmplitude
  have hs0 : L / Real.sqrt (k : ℝ) ≤ s := by
    have hsq : (L / Real.sqrt (k : ℝ)) ^ 2 ≤ s ^ 2 := by
      rw [div_pow, Real.sq_sqrt hkR.le]
      exact (div_le_iff₀ hkR).mpr (by simpa only [mul_comm] using hdim)
    nlinarith [div_nonneg hL hsqrt.le]
  constructor
  · rw [heStrong]
    calc
      _ ≤ 4 * (L / 4) ^ p := by nlinarith [hstrong.1, hbaseStrong]
      _ ≤ _ := quarter_power_budget hL hp
  · rw [heWeak]
    calc
      _ ≤ 4 * ((L / Real.sqrt k) / 4) ^ p := by nlinarith [hweak.1, hweak.2]
      _ ≤ (L / Real.sqrt k) ^ p := quarter_power_budget (by positivity) hp
      _ ≤ s ^ p := Real.rpow_le_rpow (by positivity) hs0 (by linarith)

theorem tuned_maskedKernel_two_moment {k : ℕ} (hk : 0 < k) {G L s p π : ℝ}
    (hG : 0 ≤ G) (hL : 0 ≤ L) (hs : 0 ≤ s) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hπ : 0 < π) (hkπ : (k : ℝ) * π ≤ 1) (hdim : L ^ 2 ≤ (k : ℝ) * s ^ 2)
    (ρ : ℝ) (v : Fin k → Bool) (x : HardSpace k) :
    (∫ y, ‖y - ∫ z, z ∂maskedKernel (maskedAmplitude G L p k π) ρ π hπ.le hkπ v x‖ ^ p
      ∂maskedKernel (maskedAmplitude G L p k π) ρ π hπ.le hkπ v x) ≤ L ^ p ∧
    ∀ w : HardSpace k, ‖w‖ = 1 →
      (∫ y, |⟪w, y - ∫ z, z ∂maskedKernel (maskedAmplitude G L p k π) ρ π hπ.le hkπ v x⟫_ℝ| ^ p
        ∂maskedKernel (maskedAmplitude G L p k π) ρ π hπ.le hkπ v x) ≤ s ^ p := by
  have ha := maskedAmplitude_nonneg (p := p) hG hL hπ.le k
  have hm := maskedKernel_centered_moments hk ha hπ hkπ hp hp2 ρ v x
  have hb := masked_scalar_budgets hk hL hs hp hπ hkπ hdim ha (min_le_right _ _)
  exact ⟨hm.1.trans hb.1, fun w hw => (hm.2 w hw).trans hb.2⟩

end
end HeavyTail.MaskedLower
