import Nonsmooth.SoftSliceRegularity

open Set Filter
open scoped Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem softplus_slope_mul_abs_le (v g : ℝ) : |softplusSlope v * g| ≤ |g| := by
  rw [abs_mul, abs_of_pos (softplusSlope_bounds v).1]
  exact mul_le_of_le_one_left (abs_nonneg g) (softplusSlope_bounds v).2.le

theorem softplus_hessian_term_abs_le (v g h : ℝ) :
    |softplusCurvature v * g ^ 2 + softplusSlope v * h| ≤ g ^ 2 + |h| := by
  have hc : |softplusCurvature v * g ^ 2| ≤ g ^ 2 := by
    rw [abs_mul, abs_of_pos (softplusCurvature_bounds v).1, abs_of_nonneg (sq_nonneg g)]
    exact mul_le_of_le_one_left (sq_nonneg g) ((softplusCurvature_bounds v).2.trans (by norm_num))
  exact (abs_add_le _ _).trans (add_le_add hc (softplus_slope_mul_abs_le v h))

theorem softSlice_score_growth_bound {ι : Type} [Fintype ι]
    (ρ : ℝ) (D : SmoothSliceConstraints ι) (t : ℝ) {T C : ℝ}
    (hC : 0 ≤ C) (ht : |t| ≤ T)
    (hb : ∀ i x, |D.dt i t x| ≤ C * (1 + |x| ^ 2)) (x : ℝ) :
    |softSliceScore ρ D t x| ≤ (|ρ| * T + (Fintype.card ι : ℝ) * C) * (1 + |x| ^ 2) := by
  have hT : 0 ≤ T := (abs_nonneg t).trans ht
  have hs : |∑ i, softplusSlope (D.value i t x) * D.dt i t x| ≤
      (Fintype.card ι : ℝ) * (C * (1 + |x| ^ 2)) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ i : ι, C * (1 + |x| ^ 2) := Finset.sum_le_sum (fun i _ =>
        (softplus_slope_mul_abs_le (D.value i t x) (D.dt i t x)).trans (hb i x))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hρt : |ρ * t| ≤ |ρ| * T := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left ht (abs_nonneg ρ)
  have ha := (abs_add_le (ρ * t) (∑ i, softplusSlope (D.value i t x) * D.dt i t x)).trans
    (add_le_add hρt hs)
  have hp := mul_nonneg (mul_nonneg (abs_nonneg ρ) hT) (sq_nonneg |x|)
  dsimp only [softSliceScore]
  nlinarith

theorem softSlice_gamma_growth_bound {ι : Type} [Fintype ι]
    (ρ : ℝ) (D : SmoothSliceConstraints ι) (t : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i x, |D.dt i t x| ≤ C * (1 + |x| ^ 2))
    (hbb : ∀ i x, |D.dtt i t x| ≤ C) (x : ℝ) :
    |softSliceGamma ρ D t x| ≤
      (|ρ| + (Fintype.card ι : ℝ) * (2 * C ^ 2 + C)) * (1 + |x| ^ 4) := by
  have hi (i : ι) :
      |softplusCurvature (D.value i t x) * (D.dt i t x) ^ 2 + softplusSlope (D.value i t x) * D.dtt i t x| ≤
        (2 * C ^ 2 + C) * (1 + |x| ^ 4) := by
    have hsq := polynomial_growth_square (D.dt i t) hC (hb i) x
    simp only [show 2 * 2 = 4 from rfl, abs_of_nonneg (sq_nonneg (D.dt i t x))] at hsq
    have h := (softplus_hessian_term_abs_le (D.value i t x) (D.dt i t x) (D.dtt i t x)).trans
      (add_le_add hsq (hbb i x))
    nlinarith [mul_nonneg hC (pow_nonneg (abs_nonneg x) 4)]
  have hs : |∑ i, (softplusCurvature (D.value i t x) * (D.dt i t x) ^ 2 +
      softplusSlope (D.value i t x) * D.dtt i t x)| ≤
        (Fintype.card ι : ℝ) * ((2 * C ^ 2 + C) * (1 + |x| ^ 4)) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ i : ι, (2 * C ^ 2 + C) * (1 + |x| ^ 4) := Finset.sum_le_sum (fun i _ => hi i)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have ha := (abs_add_le ρ (∑ i, (softplusCurvature (D.value i t x) * (D.dt i t x) ^ 2 +
      softplusSlope (D.value i t x) * D.dtt i t x))).trans (add_le_add le_rfl hs)
  dsimp only [softSliceGamma]
  nlinarith [mul_nonneg (abs_nonneg ρ) (pow_nonneg (abs_nonneg x) 4)]

end
end Nonsmooth
