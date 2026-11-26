import HeavyTail.HardFamily

/-! Pointwise neighboring-hypothesis separation for the actual selected
subgradient. This supplies the local signal size for a Gaussian change-of-law
argument, but does not assert a transcript information or testing bound. -/

open scoped BigOperators
namespace HeavyTail
noncomputable section

def gaussianSigns {k : ℕ} (v : Fin k → Bool) : Fin k → ℝ :=
  fun i ↦ if v i then 1 else -1

def gaussianFlip {k : ℕ} (v : Fin k → Bool) (j : Fin k) : Fin k → Bool :=
  Function.update v j (!v j)

lemma gaussianSigns_mem {k : ℕ} (v : Fin k → Bool) (i : Fin k) :
    gaussianSigns v i = -1 ∨ gaussianSigns v i = 1 := by
  cases h : v i <;> simp [gaussianSigns, h]

lemma real_sign_gap_square (x y : ℝ) : (Real.sign x - Real.sign y) ^ 2 ≤ 4 := by
  rcases Real.sign_apply_eq x with hx | hx | hx <;>
    rcases Real.sign_apply_eq y with hy | hy | hy <;> rw [hx, hy] <;> norm_num

theorem gaussian_neighbor_gradient_agrees {k : ℕ} (a ρ : ℝ)
    (v : Fin k → Bool) (j i : Fin k) (hij : i ≠ j) (x : HardSpace k) :
    hardGradient a ρ (gaussianSigns v) x i =
      hardGradient a ρ (gaussianSigns (gaussianFlip v j)) x i := by
  simp [hardGradient, gaussianSigns, gaussianFlip, Function.update_of_ne hij]

theorem gaussian_neighbor_gradient_square {k : ℕ} (a ρ : ℝ)
    (v : Fin k → Bool) (j : Fin k) (x : HardSpace k) :
    ‖hardGradient a ρ (gaussianSigns v) x -
      hardGradient a ρ (gaussianSigns (gaussianFlip v j)) x‖ ^ 2 ≤ 4 * a ^ 2 / k := by
  let g := hardGradient a ρ (gaussianSigns v) x
  let g' := hardGradient a ρ (gaussianSigns (gaussianFlip v j)) x
  have hsum : ‖g - g'‖ ^ 2 = (g j - g' j) ^ 2 := by
    rw [hardSpace_norm_sq]
    simp only [PiLp.sub_apply]
    apply Finset.sum_eq_single j
    · intro i hi hij
      have he : g i = g' i := gaussian_neighbor_gradient_agrees a ρ v j i hij x
      rw [he, sub_self]
      norm_num
    · simp
  change ‖g - g'‖ ^ 2 ≤ _
  rw [hsum]
  have hs := real_sign_gap_square (x j - ρ * gaussianSigns v j)
    (x j - ρ * gaussianSigns (gaussianFlip v j) j)
  have hmul := mul_le_mul_of_nonneg_left hs (sq_nonneg (a / Real.sqrt (k : ℝ)))
  have he : (g j - g' j) ^ 2 = (a / Real.sqrt (k : ℝ)) ^ 2 *
      (Real.sign (x j - ρ * gaussianSigns v j) -
        Real.sign (x j - ρ * gaussianSigns (gaussianFlip v j) j)) ^ 2 := by
    change ((a / Real.sqrt (k : ℝ)) * Real.sign (x j - ρ * gaussianSigns v j) -
      (a / Real.sqrt (k : ℝ)) *
        Real.sign (x j - ρ * gaussianSigns (gaussianFlip v j) j)) ^ 2 = _
    ring
  rw [he]
  calc
    _ ≤ (a / Real.sqrt (k : ℝ)) ^ 2 * 4 := hmul
    _ = 4 * a ^ 2 / k := by
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
      ring

/-- The neighboring squared signal normalized by the actual covariance. -/
theorem gaussian_neighbor_normalized_signal {k : ℕ} (hk : 0 < k) {L : ℝ} (hL : 0 < L)
    (a ρ : ℝ) (v : Fin k → Bool) (j : Fin k) (x : HardSpace k) :
    ‖hardGradient a ρ (gaussianSigns v) x -
      hardGradient a ρ (gaussianSigns (gaussianFlip v j)) x‖ ^ 2 /
        (L / Real.sqrt k) ^ 2 ≤ 4 * a ^ 2 / L ^ 2 := by
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hvar : (L / Real.sqrt (k : ℝ)) ^ 2 = L ^ 2 / k := by
    rw [div_pow, Real.sq_sqrt hkR.le]
  have h := div_le_div_of_nonneg_right (gaussian_neighbor_gradient_square a ρ v j x)
    (sq_nonneg (L / Real.sqrt (k : ℝ)))
  exact h.trans_eq (by rw [hvar]; field_simp)

end
end HeavyTail
