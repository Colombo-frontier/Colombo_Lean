import FullJet.ScaleParameters

namespace FullJet

noncomputable def accuracyWork (p : ℕ) (Δ L ε : ℝ) : ℝ :=
  Δ * L ^ (1 / (p : ℝ)) * ε ^ (-(1 + 1 / (p : ℝ)))

noncomputable def accuracyRate (p n : ℕ) (Δ L ε : ℝ) : ℝ :=
  (n : ℝ) ^ (1 - 1 / (2 * (p : ℝ))) * accuracyWork p Δ L ε

noncomputable def fullRate (p n : ℕ) (Δ L ε : ℝ) : ℝ := n + accuracyRate p n Δ L ε

noncomputable def capacityConstant (p : ℕ) : ℝ :=
  (64 * (32 * scaleConstant p) ^ (1 / (p : ℝ)))⁻¹

theorem capacityConstant_pos (p : ℕ) : 0 < capacityConstant p := by
  have hH := scaleConstant_pos p
  unfold capacityConstant
  positivity

theorem accuracyWork_pos (p : ℕ) (Δ L ε : ℝ) (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε) :
    0 < accuracyWork p Δ L ε := by unfold accuracyWork; positivity

theorem accuracyRate_nonneg (p n : ℕ) (Δ L ε : ℝ) (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε) :
    0 ≤ accuracyRate p n Δ L ε :=
  mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (accuracyWork_pos p Δ L ε hΔ hL hε).le

theorem accuracyWork_eq_manuscript (p : ℕ) (hp : 0 < p) (Δ L ε : ℝ) :
    accuracyWork p Δ L ε = Δ * L ^ (1 / (p : ℝ)) * ε ^ (-((p : ℝ) + 1) / p) := by
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold accuracyWork
  congr 2
  field_simp
  <;> ring

/-- The chosen scale has the exact precision, smoothness, and bias exponents. -/
theorem chainStageCapacity_eq (p : ℕ) (Δ L ρ ε : ℝ)
    (hL : 0 < L) (hρ : 0 < ρ) (hε : 0 < ε) :
    chainStageCapacity p Δ L ρ ε = capacityConstant p * accuracyWork p Δ L ε * ρ ^ (1 / (p : ℝ)) := by
  have hH := scaleConstant_pos p
  have h32 : 0 < 32 * scaleConstant p := mul_pos (by norm_num) hH
  have hLpow := Real.rpow_pos_of_pos hL (1 / (p : ℝ))
  have hρpow := Real.rpow_pos_of_pos hρ (1 / (p : ℝ))
  have hεpow := Real.rpow_pos_of_pos hε (1 / (p : ℝ))
  have hHpow := Real.rpow_pos_of_pos h32 (1 / (p : ℝ))
  unfold chainStageCapacity chainAlpha chainBeta capacityConstant accuracyWork
  rw [Real.div_rpow (mul_pos hL hρ).le (mul_pos h32 hε).le,
    Real.mul_rpow hL.le hρ.le, Real.mul_rpow h32.le hε.le,
    Real.rpow_neg hε.le, Real.rpow_add hε, Real.rpow_one]
  field_simp
  <;> ring

theorem sqrt_div_eq_negative_half (n : ℝ) (hn : 0 < n) :
    Real.sqrt n / n = n ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow]
  have h := Real.rpow_sub hn (1 / 2) 1
  norm_num at h
  exact h.symm

/-- The parity-compatible numerator preserves the optimized exponent even
though it is an integer rather than the formal continuous optimizer. -/
theorem capacity_dominates_accuracy (p n m : ℕ) (hp : 0 < p) (hn : 0 < n) (hm : 0 < m)
    (hlow : Real.sqrt n ≤ m) (Δ L ε : ℝ) (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε) :
    capacityConstant p * accuracyRate p n Δ L ε ≤
      (n : ℝ) * chainStageCapacity p Δ L ((m : ℝ) / n) ε := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hρ : 0 < (m : ℝ) / n := by positivity
  have hbase : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (m : ℝ) / n := by
    rw [← sqrt_div_eq_negative_half _ hn']
    exact div_le_div_of_nonneg_right hlow hn'.le
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hn'.le _) hbase
    (show 0 ≤ 1 / (p : ℝ) by positivity)
  rw [← Real.rpow_mul hn'.le] at hpow
  have hexp : (-(1 / 2 : ℝ)) * (1 / (p : ℝ)) = -(1 / (2 * (p : ℝ))) := by ring
  rw [hexp] at hpow
  have hmult := mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (mul_nonneg hn'.le (capacityConstant_pos p).le)
      (accuracyWork_pos p Δ L ε hΔ hL hε).le)
  rw [chainStageCapacity_eq p Δ L _ ε hL hρ hε]
  have hcombine : (n : ℝ) * (n : ℝ) ^ (-(1 / (2 * (p : ℝ)))) =
      (n : ℝ) ^ (1 - 1 / (2 * (p : ℝ))) := by
    conv_lhs => lhs; rw [← Real.rpow_one (n : ℝ)]
    rw [← Real.rpow_add hn']
    simp only [sub_eq_add_neg]
  calc
    _ = ((n : ℝ) * capacityConstant p * accuracyWork p Δ L ε) *
        (n : ℝ) ^ (-(1 / (2 * (p : ℝ)))) := by
      unfold accuracyRate
      rw [← hcombine]
      ring
    _ ≤ _ := hmult
    _ = _ := by ring

end FullJet
