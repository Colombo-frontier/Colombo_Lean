import LowRank.TailPowerBudget

/-! A head-dependent Ritz error compensates for the positive Schatten
power derivative. Choosing the boost degree using p bounds loss by tail power. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem power_weighted_head_decay_le {L x r : ℝ} (u : ℕ)
    (hL : 0 < L) (hx : L ≤ x) (hr : r ≤ ((2 * u : ℕ) : ℝ)) :
    (L / x) ^ (2 * u) * x ^ r ≤ L ^ r := by
  have hx0 : 0 < x := hL.trans_le hx
  have hratio : 0 < L / x := div_pos hL hx0
  have hratio1 : L / x ≤ 1 := (div_le_one hx0).mpr hx
  have h := Real.rpow_le_rpow_of_exponent_ge hratio hratio1 hr
  rw [Real.rpow_natCast] at h
  calc
    _ ≤ (L / x) ^ r * x ^ r := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hx0.le r)
    _ = L ^ r := by rw [← Real.mul_rpow hratio.le hx0.le, div_mul_cancel₀ _ hx0.ne']

theorem power_weighted_tail_loss_le {k : ℕ} (x : Fin k → ℝ) (u : ℕ) {p δ L : ℝ}
    (hp : 0 < p) (hu : p / 2 - 1 ≤ ((2 * u : ℕ) : ℝ)) (hδ : 0 ≤ δ) (hL : 0 ≤ L)
    (hx : ∀ j, L ≤ x j) :
    (∑ j, max 1 (p / 2) * (δ * L * (L / x j) ^ (2 * u)) * x j ^ (p / 2 - 1)) ≤
      max 1 (p / 2) * (k : ℝ) * δ * L ^ (p / 2) := by
  rcases eq_or_lt_of_le hL with hL | hL
  · simp only [← hL, mul_zero, zero_mul, Real.zero_rpow (by linarith : p / 2 ≠ 0), Finset.sum_const_zero]
    exact le_refl _
  · calc
      _ ≤ ∑ _ : Fin k, max 1 (p / 2) * δ * L ^ (p / 2) := by
        apply Finset.sum_le_sum
        intro j _
        calc
          _ = (max 1 (p / 2) * δ * L) * ((L / x j) ^ (2 * u) * x j ^ (p / 2 - 1)) := by ring
          _ ≤ (max 1 (p / 2) * δ * L) * L ^ (p / 2 - 1) :=
            mul_le_mul_of_nonneg_left (power_weighted_head_decay_le u hL (hx j) hu) (by positivity)
          _ = _ := by
            rw [mul_assoc, mul_rpow_sub_one_of_nonneg hL.le (by positivity : 0 < p / 2)]
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem optimalColumnSelector_power_weighted_tail_deficit {a b c k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) (M : Matrix (Fin c) (Fin b) ℝ) (u : ℕ)
    {p δ L : ℝ} (hp : 0 < p) (hu : p / 2 - 1 ≤ ((2 * u : ℕ) : ℝ)) (hδ : 0 ≤ δ) (hL : 0 ≤ L)
    (hhead : ∀ j : Fin k, L ≤
      (canonicalOrderedSpectrum b (symmetricRightGram A)).value (lastColumnIndex b k hk j))
    (happrox : ∀ j : Fin k,
      let x := (canonicalOrderedSpectrum b (symmetricRightGram A)).value (lastColumnIndex b k hk j)
      x - δ * L * (L / x) ^ (2 * u) ≤
        (canonicalOrderedSpectrum b (symmetricRightGram M)).value (lastColumnIndex b k hk j)) :
    schattenPower p (A * optimalColumnSelector a b k hk A) - max 1 (p / 2) * (k : ℝ) * δ * L ^ (p / 2) ≤
      schattenPower p (M * optimalColumnSelector c b k hk M) := by
  let x := fun j : Fin k => (canonicalOrderedSpectrum b (symmetricRightGram A)).value (lastColumnIndex b k hk j)
  have hx (j : Fin k) : 0 ≤ x j :=
    (canonicalOrderedSpectrum b (symmetricRightGram A)).value_nonneg (rightGram_posSemidef A) _
  have h := optimalColumnSelector_power_deficit hk M hp x (fun j => δ * L * (L / x j) ^ (2 * u)) hx
    (fun j => mul_nonneg (mul_nonneg hδ hL) (pow_nonneg (div_nonneg hL (hx j)) _)) happrox
  have hb := power_weighted_tail_loss_le x u hp hu hδ hL hhead
  rw [← optimalColumnSelector_schattenPower hk A p] at h
  linarith

end
end LowRank
