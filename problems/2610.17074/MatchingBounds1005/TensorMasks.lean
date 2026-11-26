import MatchingBounds1005.TensorPolynomial

/-! The manuscript's actual cubic-plus-quartic perturbation, including the
1/3 and 1/4 normalizations. -/
noncomputable section
open scoped ContDiff InnerProductSpace

namespace MatchingBounds1005.TensorGeometry

def mask {d : ℕ} (T₃ : Tensor d 3) (T₄ : Tensor d 4) (x : Vec d) : ℝ :=
  (1 / 3) * polynomial T₃ x + (1 / 4) * polynomial T₄ x

theorem mask_smooth {d : ℕ} (T₃ : Tensor d 3) (T₄ : Tensor d 4) :
    ContDiff ℝ ∞ (mask T₃ T₄) :=
  (contDiff_const.mul (polynomial_smooth T₃)).add
    (contDiff_const.mul (polynomial_smooth T₄))

theorem mask_derivative_bound {d : ℕ} (T₃ : Tensor d 3) (T₄ : Tensor d 4)
    (n : ℕ) (x : Vec d) :
    ‖iteratedFDeriv ℝ n (mask T₃ T₄) x‖ ≤
      (1 / 3 : ℝ) * (3 : ℕ).descFactorial n * ‖tensorForm T₃‖ * ‖x‖ ^ (3 - n) +
      (1 / 4 : ℝ) * (4 : ℕ).descFactorial n * ‖tensorForm T₄‖ * ‖x‖ ^ (4 - n) := by
  have hlevel : (n : WithTop ℕ∞) ≤ ∞ :=
    by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top)
  have h₃ : ContDiff ℝ n (polynomial T₃) := (polynomial_smooth T₃).of_le hlevel
  have h₄ : ContDiff ℝ n (polynomial T₄) := (polynomial_smooth T₄).of_le hlevel
  have hs₃ : ContDiff ℝ n ((1 / 3 : ℝ) • polynomial T₃) := contDiff_const.smul h₃
  have hs₄ : ContDiff ℝ n ((1 / 4 : ℝ) • polynomial T₄) := contDiff_const.smul h₄
  have he : mask T₃ T₄ = (1 / 3 : ℝ) • polynomial T₃ + (1 / 4 : ℝ) • polynomial T₄ := rfl
  rw [he, iteratedFDeriv_add_apply hs₃.contDiffAt hs₄.contDiffAt,
    iteratedFDeriv_const_smul_apply h₃.contDiffAt,
    iteratedFDeriv_const_smul_apply h₄.contDiffAt]
  apply (norm_add_le _ _).trans
  rw [norm_smul (1 / 3 : ℝ) (iteratedFDeriv ℝ n (polynomial T₃) x),
    norm_smul (1 / 4 : ℝ) (iteratedFDeriv ℝ n (polynomial T₄) x)]
  norm_num [Real.norm_eq_abs]
  have h₃b := mul_le_mul_of_nonneg_left (polynomial_derivative_bound T₃ n x)
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have h₄b := mul_le_mul_of_nonneg_left (polynomial_derivative_bound T₄ n x)
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  calc
    _ ≤ (1 / 3 : ℝ) * ((3 : ℕ).descFactorial n * ‖tensorForm T₃‖ * ‖x‖ ^ (3 - n)) +
        (1 / 4 : ℝ) * ((4 : ℕ).descFactorial n * ‖tensorForm T₄‖ * ‖x‖ ^ (4 - n)) :=
      add_le_add h₃b h₄b
    _ = _ := by ring

theorem first_jet_norm_eq_gradient {d : ℕ} (f : Vec d → ℝ) (x : Vec d) :
    ‖iteratedFDeriv ℝ 1 f x‖ = ‖gradient f x‖ := by
  rw [gradient, LinearIsometryEquiv.norm_map]
  have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (x := x) (n := 0)
  simpa only [norm_iteratedFDeriv_zero, zero_add] using h.symm

theorem mask_gradient_bound {d : ℕ} (T₃ : Tensor d 3) (T₄ : Tensor d 4)
    {δ₃ δ₄ R : ℝ} (h₃ : ‖tensorForm T₃‖ ≤ δ₃) (h₄ : ‖tensorForm T₄‖ ≤ δ₄)
    (hR : 0 ≤ R) (x : Vec d) (hx : ‖x‖ ≤ R) :
    ‖gradient (mask T₃ T₄) x‖ ≤ δ₃ * R ^ 2 + δ₄ * R ^ 3 := by
  have hd₃ : 0 ≤ δ₃ := (norm_nonneg _).trans h₃
  have hd₄ : 0 ≤ δ₄ := (norm_nonneg _).trans h₄
  have h := mask_derivative_bound T₃ T₄ 1 x
  rw [first_jet_norm_eq_gradient] at h
  norm_num only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero,
    Nat.sub_self, Nat.sub_add_cancel, Nat.cast_ofNat, Nat.cast_one, mul_one] at h
  norm_num at h
  apply h.trans
  gcongr

theorem mask_value_bound {d : ℕ} (T₃ : Tensor d 3) (T₄ : Tensor d 4)
    {δ₃ δ₄ R : ℝ} (h₃ : ‖tensorForm T₃‖ ≤ δ₃) (h₄ : ‖tensorForm T₄‖ ≤ δ₄)
    (hR : 0 ≤ R) (x : Vec d) (hx : ‖x‖ ≤ R) :
    |mask T₃ T₄ x| ≤ δ₃ * R ^ 3 / 3 + δ₄ * R ^ 4 / 4 := by
  have hd₃ : 0 ≤ δ₃ := (norm_nonneg _).trans h₃
  have hd₄ : 0 ≤ δ₄ := (norm_nonneg _).trans h₄
  have h := mask_derivative_bound T₃ T₄ 0 x
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, Nat.descFactorial_zero,
    Nat.cast_one, mul_one, Nat.sub_zero] at h
  apply h.trans
  calc
    _ ≤ (1 / 3 : ℝ) * δ₃ * R ^ 3 + (1 / 4 : ℝ) * δ₄ * R ^ 4 := by gcongr
    _ = _ := by ring

theorem mask_radial_pairing_bound {d : ℕ} (T₃ : Tensor d 3) (T₄ : Tensor d 4)
    {δ₃ δ₄ R : ℝ} (h₃ : ‖tensorForm T₃‖ ≤ δ₃) (h₄ : ‖tensorForm T₄‖ ≤ δ₄)
    (hR : 0 ≤ R) (x : Vec d) (hx : ‖x‖ ≤ R) :
    |⟪x, gradient (mask T₃ T₄) x⟫_ℝ| ≤ R * (δ₃ * R ^ 2 + δ₄ * R ^ 3) := by
  apply (abs_real_inner_le_norm x _).trans
  exact mul_le_mul hx (mask_gradient_bound T₃ T₄ h₃ h₄ hR x hx) (norm_nonneg _)
    hR

end MatchingBounds1005.TensorGeometry


