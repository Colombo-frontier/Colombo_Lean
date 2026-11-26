import LowRank.GaussianInverseGramRotation

/-! The inverse Gram quadratic law for arbitrary fixed vectors, including
zero, in a form suitable for integrating over a second Gaussian vector. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

theorem normalizeVector_reconstruct {s : ℕ} (w : Fin s → ℝ) (hw : w ≠ 0) :
    Real.sqrt (w ⬝ᵥ w) • normalizeVector w = w := by
  have hnonneg : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg (fun i _ => mul_self_nonneg (w i))
  have hpos : 0 < w ⬝ᵥ w := lt_of_le_of_ne hnonneg (fun h => hw (dotProduct_self_eq_zero.mp h.symm))
  rw [normalizeVector, smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.mpr hpos).ne', one_smul]

theorem quadratic_normalizeVector {s : ℕ} (H : Matrix (Fin s) (Fin s) ℝ)
    (w : Fin s → ℝ) (hw : w ≠ 0) :
    w ⬝ᵥ (H *ᵥ w) = (w ⬝ᵥ w) * (normalizeVector w ⬝ᵥ (H *ᵥ normalizeVector w)) := by
  have hnonneg : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg (fun i _ => mul_self_nonneg (w i))
  calc
    _ = (Real.sqrt (w ⬝ᵥ w) • normalizeVector w) ⬝ᵥ
        (H *ᵥ (Real.sqrt (w ⬝ᵥ w) • normalizeVector w)) := by rw [normalizeVector_reconstruct w hw]
    _ = Real.sqrt (w ⬝ᵥ w) ^ 2 * (normalizeVector w ⬝ᵥ (H *ᵥ normalizeVector w)) := by
      rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
      simp only [smul_eq_mul]
      ring
    _ = _ := by rw [Real.sq_sqrt hnonneg]

theorem measurable_inverseGram_quadratic (d s : ℕ) (w : Fin s → ℝ) :
    Measurable (fun X : Matrix (Fin d) (Fin s) ℝ => w ⬝ᵥ (inverseGram X *ᵥ w)) := by
  have hG := measurable_inverseGram d s
  simp only [dotProduct, Matrix.mulVec]
  fun_prop

theorem iidMatrixLaw_inverseGram_quadratic {d s : ℕ} (hs : s + 1 ≤ d)
    {v : NNReal} (hv : v ≠ 0) (w : Fin (s + 1) → ℝ) :
    (iidMatrixLaw d (s + 1) v).map (fun X => w ⬝ᵥ (inverseGram X *ᵥ w)) =
      (squaredGaussianLaw (d - s) v).map (fun t : ℝ => (w ⬝ᵥ w) * t⁻¹) := by
  by_cases hw : w = 0
  · subst w
    simp
  · have hunit := iidMatrixLaw_inverseGram_unit_quadratic hs hv (normalizeVector w)
      (normalizeVector_dot_self w hw)
    have hscale : Measurable (fun t : ℝ => (w ⬝ᵥ w) * t) := measurable_const.mul measurable_id
    simp_rw [quadratic_normalizeVector _ w hw]
    change (iidMatrixLaw d (s + 1) v).map
      ((fun t : ℝ => (w ⬝ᵥ w) * t) ∘ (fun X => normalizeVector w ⬝ᵥ (inverseGram X *ᵥ normalizeVector w))) = _
    rw [← Measure.map_map hscale
      (measurable_inverseGram_quadratic d (s + 1) (normalizeVector w)), hunit,
      Measure.map_map hscale measurable_inv]
    rfl

end
end LowRank
