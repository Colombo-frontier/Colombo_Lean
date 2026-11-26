import MatchingBounds1005.TensorMasks
import MatchingBounds1005.RadialComposition

/-! Radius-uniform derivative estimates for the actual confined polynomial mask. -/
noncomputable section
open scoped ContDiff BigOperators

namespace MatchingBounds1005.TensorGeometry

theorem small_descFactorial_le {k j : ℕ} (hk : k ≤ 4) : k.descFactorial j ≤ 24 := by
  by_cases hj : k < j
  · simp [Nat.descFactorial_of_lt hj]
  · have hj4 : j ≤ 4 := by omega
    interval_cases k <;> interval_cases j <;> norm_num

theorem weighted_polynomial_jet {d k j : ℕ} (hk : k ≤ 4) (T : Tensor d k)
    {R : ℝ} (hR : 0 ≤ R) :
    (k.descFactorial j : ℝ) * ‖tensorForm T‖ * R ^ (k - j) * R ^ j ≤
      24 * ‖tensorForm T‖ * R ^ k := by
  by_cases hj : k < j
  · simp only [Nat.descFactorial_of_lt hj, Nat.cast_zero, zero_mul]
    positivity
  · have hjk : j ≤ k := by omega
    rw [mul_assoc ((k.descFactorial j : ℝ) * ‖tensorForm T‖), ← pow_add,
      Nat.sub_add_cancel hjk]
    have hfac : (k.descFactorial j : ℝ) ≤ 24 := by exact_mod_cast small_descFactorial_le (j := j) hk
    gcongr

theorem polynomial_radial_derivative_bound {d k n : ℕ} (hk : k ≤ 4) (hn : 1 ≤ n)
    (T : Tensor d k) {R : ℝ} (hR : 0 < R) (x : Vec d) :
    ‖iteratedFDeriv ℝ n (polynomial T ∘ radial R) x‖ ≤
      (24 * n * RadialHigher.compositionConstant n) * ‖tensorForm T‖ * R ^ k / R ^ n := by
  have hninf : (n : WithTop ℕ∞) ≤ ∞ :=
    by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top)
  let b : ℕ → ℝ := fun j => k.descFactorial j * ‖tensorForm T‖ * R ^ (k - j)
  have hb : ∀ j, 1 ≤ j → j ≤ n → 0 ≤ b j := by
    intro j _ _
    dsimp only [b]
    positivity
  have hbound : ∀ j, 1 ≤ j → j ≤ n → ∀ y : Vec d, ‖y‖ ≤ R →
      ‖iteratedFDeriv ℝ j (polynomial T) y‖ ≤ b j := by
    intro j _ _ y hy
    exact (polynomial_derivative_bound T j y).trans (by dsimp only [b]; gcongr)
  have h := RadialHigher.radial_composition_jet_bound hn
    ((polynomial_smooth T).of_le hninf) hR b hb hbound x
  have hsum : (∑ j ∈ Finset.Icc 1 n, b j * R ^ j) ≤
      n * (24 * ‖tensorForm T‖ * R ^ k) := by
    calc
      _ ≤ ∑ _j ∈ Finset.Icc 1 n, 24 * ‖tensorForm T‖ * R ^ k :=
        Finset.sum_le_sum (fun j _ => weighted_polynomial_jet hk T hR.le)
      _ = _ := by simp
  apply h.trans
  apply div_le_div_of_nonneg_right _ (pow_nonneg hR.le n)
  have hK : 0 ≤ RadialHigher.compositionConstant n :=
    zero_le_one.trans (RadialHigher.compositionConstant_one_le n)
  exact (mul_le_mul_of_nonneg_left hsum hK).trans_eq (by ring)

/-- The perturbation budget has exactly the source radius scaling ν R^(1-n).
The numerical derivative constant depends only on the derivative order. -/
theorem mask_radial_derivative_bound {d n : ℕ} (hn : 1 ≤ n)
    (T₃ : Tensor d 3) (T₄ : Tensor d 4) {δ₃ δ₄ R : ℝ}
    (h₃ : ‖tensorForm T₃‖ ≤ δ₃) (h₄ : ‖tensorForm T₄‖ ≤ δ₄)
    (hR : 0 < R) (x : Vec d) :
    ‖iteratedFDeriv ℝ n (mask T₃ T₄ ∘ radial R) x‖ ≤
      (24 * n * RadialHigher.compositionConstant n) * (δ₃ * R ^ 3 + δ₄ * R ^ 4) / R ^ n := by
  have hninf : (n : WithTop ℕ∞) ≤ ∞ :=
    by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top)
  have hs3 : ContDiff ℝ n (polynomial T₃ ∘ radial R) :=
    ((polynomial_smooth T₃).of_le hninf).comp (radial_contDiff R n)
  have hs4 : ContDiff ℝ n (polynomial T₄ ∘ radial R) :=
    ((polynomial_smooth T₄).of_le hninf).comp (radial_contDiff R n)
  have he : mask T₃ T₄ ∘ radial R =
      (1 / 3 : ℝ) • (polynomial T₃ ∘ radial R) +
      (1 / 4 : ℝ) • (polynomial T₄ ∘ radial R) := rfl
  have hss3 : ContDiff ℝ n ((1 / 3 : ℝ) • (polynomial T₃ ∘ radial R)) :=
    contDiff_const.smul hs3
  have hss4 : ContDiff ℝ n ((1 / 4 : ℝ) • (polynomial T₄ ∘ radial R)) :=
    contDiff_const.smul hs4
  rw [he, iteratedFDeriv_add_apply hss3.contDiffAt hss4.contDiffAt,
    iteratedFDeriv_const_smul_apply hs3.contDiffAt,
    iteratedFDeriv_const_smul_apply hs4.contDiffAt]
  apply (norm_add_le _ _).trans
  rw [norm_smul, norm_smul]
  norm_num [Real.norm_eq_abs]
  have h3 := polynomial_radial_derivative_bound (by omega : 3 ≤ 4) hn T₃ hR x
  have h4 := polynomial_radial_derivative_bound (by omega : 4 ≤ 4) hn T₄ hR x
  have hK : 0 ≤ 24 * (n : ℝ) * RadialHigher.compositionConstant n :=
    mul_nonneg (by positivity) (zero_le_one.trans (RadialHigher.compositionConstant_one_le n))
  have hb3 : ‖iteratedFDeriv ℝ n (polynomial T₃ ∘ radial R) x‖ ≤
      (24 * n * RadialHigher.compositionConstant n) * δ₃ * R ^ 3 / R ^ n :=
    h3.trans (by gcongr)
  have hb4 : ‖iteratedFDeriv ℝ n (polynomial T₄ ∘ radial R) x‖ ≤
      (24 * n * RadialHigher.compositionConstant n) * δ₄ * R ^ 4 / R ^ n :=
    h4.trans (by gcongr)
  have hsum := add_le_add hb3 hb4
  have hnorm3 := norm_nonneg (iteratedFDeriv ℝ n (polynomial T₃ ∘ radial R) x)
  have hnorm4 := norm_nonneg (iteratedFDeriv ℝ n (polynomial T₄ ∘ radial R) x)
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (polynomial T₃ ∘ radial R) x‖ +
        ‖iteratedFDeriv ℝ n (polynomial T₄ ∘ radial R) x‖ := by linarith
    _ ≤ _ := hsum.trans_eq (by ring)

end MatchingBounds1005.TensorGeometry



