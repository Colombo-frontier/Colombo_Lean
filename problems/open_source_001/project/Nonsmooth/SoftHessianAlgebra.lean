import Nonsmooth.SoftplusDerivatives

open Set Filter
open scoped Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem two_dimensional_hessian_from_quadratic_lower {a b c ρ : ℝ} (hρ : 1 < ρ)
    (h : ∀ p q : ℝ, ρ * (p ^ 2 + q ^ 2) ≤ a * p ^ 2 + 2 * b * p * q + c * q ^ 2) :
    0 < a - 1 ∧ b ^ 2 ≤ (a - 1) * (c - 1) := by
  have ha : 0 < a - 1 := by have h0 := h 1 0; norm_num at h0; linarith
  refine ⟨ha, ?_⟩
  have hpsd (p q : ℝ) : 0 ≤ (a - 1) * p ^ 2 + 2 * b * p * q + (c - 1) * q ^ 2 := by
    have hm := mul_nonneg (sub_nonneg.mpr hρ.le) (add_nonneg (sq_nonneg p) (sq_nonneg q))
    nlinarith [h p q]
  have hp : 0 ≤ (a - 1) * ((a - 1) * (c - 1) - b ^ 2) := by
    nlinarith [hpsd b (-(a - 1))]
  by_contra hn
  have hh := mul_neg_of_pos_of_neg ha (sub_neg.mpr (lt_of_not_ge hn))
  linarith

theorem softplus_quadratic_second_nonneg (t p q hxx hxy hyy : ℝ)
    (h : 0 ≤ hxx * p ^ 2 + 2 * hxy * p * q + hyy * q ^ 2)
    (gx gy : ℝ) :
    0 ≤ softplusCurvature t * (gx * p + gy * q) ^ 2 +
      softplusSlope t * (hxx * p ^ 2 + 2 * hxy * p * q + hyy * q ^ 2) :=
  add_nonneg (mul_nonneg (softplusCurvature_bounds t).1.le (sq_nonneg _))
    (mul_nonneg (softplusSlope_bounds t).1.le h)

theorem softplus_finite_hessian_lower {ι : Type} [Fintype ι]
    (ρ : ℝ) (v gx gy hxx hxy hyy : ι → ℝ)
    (h : ∀ i p q, 0 ≤ hxx i * p ^ 2 + 2 * hxy i * p * q + hyy i * q ^ 2)
    (p q : ℝ) :
    ρ * (p ^ 2 + q ^ 2) ≤
      (ρ + ∑ i, (softplusCurvature (v i) * (gx i) ^ 2 + softplusSlope (v i) * hxx i)) * p ^ 2 +
      2 * (∑ i, (softplusCurvature (v i) * gx i * gy i + softplusSlope (v i) * hxy i)) * p * q +
      (ρ + ∑ i, (softplusCurvature (v i) * (gy i) ^ 2 + softplusSlope (v i) * hyy i)) * q ^ 2 := by
  have hs := Finset.sum_nonneg (s := Finset.univ) (fun i _ =>
    softplus_quadratic_second_nonneg (v i) p q (hxx i) (hxy i) (hyy i) (h i p q) (gx i) (gy i))
  have he :
      (∑ i, (softplusCurvature (v i) * (gx i * p + gy i * q) ^ 2 +
        softplusSlope (v i) * (hxx i * p ^ 2 + 2 * hxy i * p * q + hyy i * q ^ 2))) =
      (∑ i, (softplusCurvature (v i) * (gx i) ^ 2 + softplusSlope (v i) * hxx i)) * p ^ 2 +
      2 * (∑ i, (softplusCurvature (v i) * gx i * gy i + softplusSlope (v i) * hxy i)) * p * q +
      (∑ i, (softplusCurvature (v i) * (gy i) ^ 2 + softplusSlope (v i) * hyy i)) * q ^ 2 := by
    simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he] at hs
  nlinarith

end
end Nonsmooth
