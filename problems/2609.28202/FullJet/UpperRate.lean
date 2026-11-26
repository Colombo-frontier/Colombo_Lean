import FullJet.AmplifiedMethod

namespace FullJet

noncomputable def upperFactor (p : ℕ) : ℝ := 128 * ((p + 1).factorial : ℝ)

theorem upperFactor_pos (p : ℕ) : 0 < upperFactor p := by unfold upperFactor; positivity

theorem upperErrorScale_n_one_le (p n : ℕ) (hn : 0 < n) (L : ℝ) (hL : 0 ≤ L) :
    upperErrorScale p L n 1 ≤ ((p : ℝ) + 2) * L * ((n : ℝ) ^ (p - 1) * Real.sqrt n) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt : (1 : ℝ) ≤ Real.sqrt n := by simpa using Real.sqrt_le_sqrt hn1
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ (p - 1) := one_le_pow₀ hn1
  have hLpow : L ≤ L * (n : ℝ) ^ (p - 1) := le_mul_of_one_le_right hL hpow
  have hLsqrt := le_mul_of_one_le_right (mul_nonneg hL (pow_nonneg (Nat.cast_nonneg n) (p - 1))) hsqrt
  have hDsqrt := le_mul_of_one_le_right
    (show 0 ≤ (p : ℝ) * L * (n : ℝ) ^ (p - 1) by positivity) hsqrt
  unfold upperErrorScale higherErrorCoefficient gradientNoiseCoefficient
  norm_num only [Nat.cast_one, Real.sqrt_one, div_one]
  nlinarith only [hLpow, hLsqrt, hDsqrt]

theorem nat_power_mul_sqrt (p n : ℕ) (hp : 0 < p) (hn : 0 < n) :
    (n : ℝ) ^ (p - 1) * Real.sqrt n = (n : ℝ) ^ ((p : ℝ) - 1 / 2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hn']
  congr 1
  rw [Nat.cast_sub hp, Nat.cast_one]
  ring

theorem upperModelScale_n_one_le (p n : ℕ) (hp : 0 < p) (hn : 0 < n)
    (L : ℝ) (hL : 0 ≤ L) :
    upperModelScale p L n 1 ≤ (upperFactor p * ((p : ℝ) + 2)) * L *
      (n : ℝ) ^ ((p : ℝ) - 1 / 2) := by
  have h := mul_le_mul_of_nonneg_left (upperErrorScale_n_one_le p n hn L hL) (upperFactor_pos p).le
  rw [nat_power_mul_sqrt p n hp hn] at h
  simpa only [upperModelScale, upperFactor, mul_assoc] using h

theorem upperModelScale_root_le (p n : ℕ) (hp : 0 < p) (hn : 0 < n)
    (L : ℝ) (hL : 0 < L) :
    upperModelScale p L n 1 ^ (1 / (p : ℝ)) ≤
      (upperFactor p * ((p : ℝ) + 2)) ^ (1 / (p : ℝ)) * L ^ (1 / (p : ℝ)) *
        (n : ℝ) ^ (1 - 1 / (2 * (p : ℝ))) := by
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hc : 0 ≤ upperFactor p * ((p : ℝ) + 2) := by have := upperFactor_pos p; positivity
  have h := Real.rpow_le_rpow (upperModelScale_pos p L n 1 hL).le
    (upperModelScale_n_one_le p n hp hn L hL.le) (show 0 ≤ 1 / (p : ℝ) by positivity)
  rw [Real.mul_rpow (mul_nonneg hc hL.le) (Real.rpow_nonneg (Nat.cast_nonneg n) _),
    Real.mul_rpow hc hL.le, ← Real.rpow_mul (Nat.cast_nonneg n)] at h
  have he : ((p : ℝ) - 1 / 2) * (1 / (p : ℝ)) = 1 - 1 / (2 * (p : ℝ)) := by
    field_simp
    <;> ring
  simpa only [he] using h

theorem upperWork_eq (p : ℕ) (hp : 0 < p) (Δ L ε : ℝ) (m B : ℕ)
    (hL : 0 < L) (hε : 0 < ε) :
    Δ / (upperErrorScale p L m B * upperRadius p L ε m B ^ (p + 1)) =
      (32 * upperFactor p * (32 : ℝ) ^ (1 / (p : ℝ))) *
        Δ * upperModelScale p L m B ^ (1 / (p : ℝ)) * ε ^ (-(1 + 1 / (p : ℝ))) := by
  let S := upperErrorScale p L m B
  let M := upperModelScale p L m B
  let r := upperRadius p L ε m B
  have hC := upperFactor_pos p
  have hS : 0 < S := upperErrorScale_pos p L m B hL
  have hM : 0 < M := upperModelScale_pos p L m B hL
  have hr : 0 < r := upperRadius_pos p L ε m B hL hε
  have hMr : 32 * M * r ^ p = ε := upperRadius_equation p hp L ε m B hL hε
  have hMS : M = upperFactor p * S := rfl
  have hd : S * r ^ (p + 1) = ε * r / (32 * upperFactor p) := by
    apply (eq_div_iff (by positivity : 32 * upperFactor p ≠ 0)).mpr
    calc
      _ = (32 * M * r ^ p) * r := by rw [hMS, pow_succ]; ring
      _ = ε * r := congrArg (fun z => z * r) hMr
  change Δ / (S * r ^ (p + 1)) = _
  rw [hd]
  have hrform : r = ε ^ (1 / (p : ℝ)) /
      ((32 : ℝ) ^ (1 / (p : ℝ)) * M ^ (1 / (p : ℝ))) := by
    dsimp only [r, upperRadius]
    rw [Real.div_rpow hε.le (by positivity), Real.mul_rpow (by norm_num) hM.le]
  rw [hrform, Real.rpow_neg hε.le, Real.rpow_add hε, Real.rpow_one]
  field_simp
  <;> ring

noncomputable def upperStepConstant (p : ℕ) : ℝ :=
  32 * upperFactor p * (32 : ℝ) ^ (1 / (p : ℝ)) *
    (upperFactor p * ((p : ℝ) + 2)) ^ (1 / (p : ℝ))

theorem upperStepConstant_pos (p : ℕ) : 0 < upperStepConstant p := by
  have := upperFactor_pos p
  unfold upperStepConstant
  positivity

theorem upperWork_n_one_le (p n : ℕ) (hp : 0 < p) (hn : 0 < n)
    (Δ L ε : ℝ) (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε) :
    Δ / (upperErrorScale p L n 1 * upperRadius p L ε n 1 ^ (p + 1)) ≤
      upperStepConstant p * accuracyRate p n Δ L ε := by
  rw [upperWork_eq p hp Δ L ε n 1 hL hε]
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (upperModelScale_root_le p n hp hn L hL)
      (show 0 ≤ (32 * upperFactor p * (32 : ℝ) ^ (1 / (p : ℝ))) * Δ by
        have := upperFactor_pos p; positivity))
    (Real.rpow_nonneg hε.le (-(1 + 1 / (p : ℝ))))
  convert h using 1 <;> unfold upperStepConstant accuracyRate accuracyWork <;> ring

noncomputable def mainUpperConstant (p : ℕ) : ℝ := 3 * upperStepConstant p + 4

theorem mainUpperConstant_pos (p : ℕ) : 0 < mainUpperConstant p := by
  have := upperStepConstant_pos p
  unfold mainUpperConstant
  positivity

/-- Choosing m=n and B=1 avoids integer square-root rounding and still
achieves the desired n exponent. The extra n includes exact validation. -/
theorem upperQueryBudget_with_validation_le (p n : ℕ) (hp : 0 < p) (hn : 0 < n)
    (Δ L ε : ℝ) (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε) :
    (upperQueryBudget p n Δ L ε n 1 : ℝ) + n ≤ mainUpperConstant p * fullRate p n Δ L ε := by
  have hs := upperEpochCount_steps_le p Δ L ε n 1 hΔ.le hL hε hn
  have hw := upperWork_n_one_le p n hp hn Δ L ε hΔ hL hε
  have hacc := accuracyRate_nonneg p n Δ L ε hΔ hL hε
  have hc := upperStepConstant_pos p
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  simp only [upperQueryBudget, epochQueryCost, Nat.cast_mul, Nat.cast_add,
    Nat.cast_ofNat, Nat.cast_one] at *
  unfold mainUpperConstant fullRate
  nlinarith only [hs, hw, hacc, mul_nonneg hc.le hn']

theorem verifiedQueryBudget_le (p n : ℕ) (hp : 0 < p) (hn : 0 < n)
    (Δ L ε : ℝ) (K : ℕ) (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε) :
    (verifiedQueryBudget p n Δ L ε n 1 K : ℝ) ≤
      (K : ℝ) * mainUpperConstant p * fullRate p n Δ L ε := by
  simpa only [verifiedQueryBudget, Nat.cast_mul, Nat.cast_add, mul_assoc] using
    mul_le_mul_of_nonneg_left (upperQueryBudget_with_validation_le p n hp hn Δ L ε hΔ hL hε)
      (Nat.cast_nonneg K)

end FullJet
