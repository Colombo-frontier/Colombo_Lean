import GradientHessian.SelectorCoordinateBounds

/-! Literal port jets on disjoint Hilbert coordinates, retaining the variance
factor through second order and an absolute sum estimate at third order. -/

namespace GradientHessian.SelectorPortJets
open SelectorProfileBounds SelectorPortBounds SelectorCoordinateBounds
open Classical
open scoped BigOperators
noncomputable section

variable {ι E F : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def coordinatePort (R : ℝ) (v : ι → E) (A : ι → F →L[ℝ] E) (i : ι) : F → ℝ :=
  port R (v i) ∘ A i

omit [Fintype ι] in
theorem coordinatePort_contDiff (R : ℝ) (v : ι → E) (A : ι → F →L[ℝ] E) (i : ι) :
    ContDiff ℝ 3 (coordinatePort R v A i) := (port_contDiff R (v i)).comp (A i).contDiff

omit [Fintype ι] in
theorem coordinatePort_mem (R : ℝ) (v : ι → E) (A : ι → F →L[ℝ] E) (x : F) (i : ι) :
    coordinatePort R v A i x ∈ Set.Icc (0:ℝ) 1 := Profiles.varpi_bounds _

omit [Fintype ι] in
theorem port_jet_relative {R : ℝ} (hR : 0 < R) (v : ι → E)
    (hv : ∀ i, ‖v i‖ = 1) (A : ι → F →L[ℝ] E) (x : F)
    {n : ℕ} (hn1 : 1 ≤ n) (hn2 : n ≤ 2) (w : Fin n → F) (i : ι) :
    |iteratedFDeriv ℝ n (coordinatePort R v A i) x w| ≤
      (portConstant/R^n*(∏ l, ‖A i (w l)‖))*varianceRoot (coordinatePort R v A i x) := by
  unfold coordinatePort
  rw [(A i).iteratedFDeriv_comp_right (port_contDiff R (v i)) x
    (by exact_mod_cast hn2.trans (by norm_num : 2 ≤ 3)),
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (port R (v i)) (A i x)‖ * ∏ l, ‖A i (w l)‖ := by
      exact (iteratedFDeriv ℝ n (port R (v i)) (A i x)).le_opNorm _
    _ ≤ (portConstant*varianceRoot (port R (v i) (A i x))/R^n)*∏ l, ‖A i (w l)‖ :=
      mul_le_mul_of_nonneg_right (port_relative_bound hR (v i) (A i x) (hv i) hn1 hn2)
        (Finset.prod_nonneg (fun l _ => norm_nonneg _))
    _ = _ := by simp only [Function.comp_apply]; ring

theorem port_jet_normalized_square_sum {R : ℝ} (hR : 0 < R) (v : ι → E)
    (hv : ∀ i, ‖v i‖ = 1) (A : ι → F →L[ℝ] E) (hA : CoordinateContraction A) (x : F)
    {n : ℕ} (hn1 : 1 ≤ n) (hn2 : n ≤ 2) (w : Fin n → F) :
    (∑ i, (iteratedFDeriv ℝ n (coordinatePort R v A i) x w /
      varianceRoot (coordinatePort R v A i x))^2) ≤
      (portConstant/R^n)^2*(∏ l, ‖w l‖)^2 := by
  have hC : 0 ≤ portConstant/R^n := div_nonneg (zero_le_one.trans portConstant_ge_one) (pow_nonneg hR.le _)
  calc
    _ ≤ ∑ i, (portConstant/R^n)^2*(∏ l, ‖A i (w l)‖)^2 := by
      apply Finset.sum_le_sum
      intro i _
      have h := (variance_div_factor (mul_nonneg hC (Finset.prod_nonneg (fun l _ => norm_nonneg _)))
        (port_jet_relative hR v hv A x hn1 hn2 w i)).2
      simpa only [sq_abs, mul_pow] using pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = (portConstant/R^n)^2*(∑ i, (∏ l, ‖A i (w l)‖)^2) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (coordinate_product_square_sum hA hn1 w) (sq_nonneg _)

theorem port_jet_third_sum {R : ℝ} (hR : 0 < R) (v : ι → E)
    (hv : ∀ i, ‖v i‖ = 1) (A : ι → F →L[ℝ] E) (hA : CoordinateContraction A)
    (x : F) (w : Fin 3 → F) :
    (∑ i, |iteratedFDeriv ℝ 3 (coordinatePort R v A i) x w|) ≤
      portConstant/R^3*(∏ l, ‖w l‖) := by
  have hC : 0 ≤ portConstant/R^3 := div_nonneg (zero_le_one.trans portConstant_ge_one) (pow_nonneg hR.le _)
  calc
    _ ≤ ∑ i, portConstant/R^3*(∏ l, ‖A i (w l)‖) := by
      apply Finset.sum_le_sum
      intro i _
      unfold coordinatePort
      rw [(A i).iteratedFDeriv_comp_right (port_contDiff R (v i)) x (by norm_num),
        ContinuousMultilinearMap.compContinuousLinearMap_apply]
      exact ((iteratedFDeriv ℝ 3 (port R (v i)) (A i x)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (port_third_bound hR (v i) (A i x) (hv i))
          (Finset.prod_nonneg (fun l _ => norm_nonneg _)))
    _ = portConstant/R^3*(∑ i, ∏ l, ‖A i (w l)‖) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (coordinate_triple_sum hA w) hC

end
end GradientHessian.SelectorPortJets
