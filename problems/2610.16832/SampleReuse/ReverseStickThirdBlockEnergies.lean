import SecondOrder.BlockGateEnergies
import SampleReuse.ReverseStickThirdOrthogonality

/-! Actual gate derivative energies for the third-order score estimate. -/

open SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The new weighted second-derivative hypothesis controls its Fisher energy
without a factor for the number of blocks. -/
theorem blockGate_second_fisher_energy
    (p : ι → E → ℝ) (hp : ∀ i, ContDiff ℝ 2 (p i))
    (x u v : HomogeneousBlocks ι E)
    (hp0 : ∀ i, 0 < p i (x i)) (hp1 : ∀ i, p i (x i) < 1)
    (ell₂ : ℝ)
    (hH : ∀ i, ‖fderiv ℝ (fderiv ℝ (p i)) (x i)‖ ^ 2 ≤
      ell₂ ^ 2 * p i (x i) * (1 - p i (x i))) :
    bernoulliFisherEnergy (fun i => p i (x i))
        (fun i => secondBilinear (fun y : HomogeneousBlocks ι E => p i (y i)) x u v) ≤
      ell₂ ^ 2 * ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  have hi (i : ι) :
      secondBilinear (p i) (x i) (u i) (v i) ^ 2 /
          (p i (x i) * (1 - p i (x i))) ≤ ell₂ ^ 2 * ‖u i‖ ^ 2 * ‖v i‖ ^ 2 := by
    apply (div_le_iff₀ (mul_pos (hp0 i) (sub_pos.mpr (hp1 i)))).2
    have hd := secondBilinear_abs_le (f := p i) (x i) (u i) (v i)
    have hd2 := mul_self_le_mul_self (abs_nonneg _) hd
    have hd' : secondBilinear (p i) (x i) (u i) (v i) ^ 2 ≤
        ‖fderiv ℝ (fderiv ℝ (p i)) (x i)‖ ^ 2 * ‖u i‖ ^ 2 * ‖v i‖ ^ 2 := by
      simpa only [← pow_two, sq_abs, mul_pow] using hd2
    have hh := mul_le_mul_of_nonneg_right (hH i) (mul_nonneg (sq_nonneg ‖u i‖) (sq_nonneg ‖v i‖))
    nlinarith only [hd', hh]
  unfold bernoulliFisherEnergy
  simp only [blockGate_secondBilinear p hp]
  calc
    _ ≤ ∑ i, ell₂ ^ 2 * ‖u i‖ ^ 2 * ‖v i‖ ^ 2 := Finset.sum_le_sum (fun i _ => hi i)
    _ ≤ ∑ i, ell₂ ^ 2 * ‖u i‖ ^ 2 * ‖v‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le v i) 2)
        (mul_nonneg (sq_nonneg ell₂) (sq_nonneg ‖u i‖))
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum, ← PiLp.norm_sq_eq_of_L2]

/-- The degree-one part of the third score is controlled in L¹ by this
actual third-derivative contraction estimate. -/
theorem blockGate_third_absolute_sum
    (p : ι → E → ℝ) (x u v w : HomogeneousBlocks ι E)
    {ell₃ : ℝ} (hell : 0 ≤ ell₃)
    (hthird : ∀ i, ‖iteratedFDeriv ℝ 3 (p i) (x i)‖ ≤ ell₃) :
    (∑ i, |iteratedFDeriv ℝ 3 (p i) (x i) ![u i, v i, w i]|) ≤
      ell₃ * ‖u‖ * ‖v‖ * ‖w‖ := by
  have hcs : (∑ i, ‖u i‖ * ‖v i‖) ≤ ‖u‖ * ‖v‖ := by
    have hh := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => ‖u i‖) (fun i => ‖v i‖)
    simpa only [← PiLp.norm_sq_eq_of_L2, Real.sqrt_sq (norm_nonneg _)] using hh
  calc
    _ ≤ ∑ i, ell₃ * (‖u i‖ * ‖v i‖ * ‖w i‖) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, Matrix.head_cons, Real.norm_eq_abs] using
        ContinuousMultilinearMap.le_of_opNorm_le (hthird i) ![u i, v i, w i]
    _ ≤ ∑ i, ell₃ * (‖u i‖ * ‖v i‖ * ‖w‖) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le w i)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))) hell
    _ = ell₃ * ((∑ i, ‖u i‖ * ‖v i‖) * ‖w‖) := by
      rw [← Finset.mul_sum, ← Finset.sum_mul]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hcs (norm_nonneg w)) hell
      simpa only [mul_assoc] using hh

end
end SampleReuse
