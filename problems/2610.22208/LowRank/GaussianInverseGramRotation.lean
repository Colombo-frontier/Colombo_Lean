import LowRank.GaussianInverseGramDiagonal
import LowRank.MeasurableSpectralStep

/-! Gaussian right-rotation invariance upgrades the inverse Gram diagonal
law to every fixed unit direction. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

theorem iidMatrixLaw_right_orthogonal {d s : ℕ} (O : Matrix (Fin s) (Fin s) ℝ)
    (hO : Oᵀ * O = 1) (v : NNReal) :
    (iidMatrixLaw d s v).map (fun X => X * O) = iidMatrixLaw d s v := by
  have hm : Measurable (fun x : Fin s → ℝ => Oᵀ *ᵥ x) := by
    apply measurable_pi_lambda
    intro i
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have hp := measurePreserving_pi (fun _ : Fin d => iidVectorLaw s v)
    (fun _ : Fin d => iidVectorLaw s v)
    (fun _ => (show MeasurePreserving (fun x => Oᵀ *ᵥ x) (iidVectorLaw s v) (iidVectorLaw s v) from
      ⟨hm, iidVectorLaw_orthogonal_compression O hO v⟩))
  convert hp.map_eq using 2
  funext X i j
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]

theorem inverseGram_right_orthogonal {d s : ℕ} (X : Matrix (Fin d) (Fin s) ℝ)
    (O : Matrix (Fin s) (Fin s) ℝ) (hO : Oᵀ * O = 1) :
    inverseGram (X * O) = Oᵀ * inverseGram X * O := by
  have hOi : O⁻¹ = Oᵀ := Matrix.inv_eq_left_inv hO
  have hOti : Oᵀ⁻¹ = O := Matrix.inv_eq_right_inv hO
  have hg : (X * O)ᵀ * (X * O) = Oᵀ * (Xᵀ * X) * O := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [inverseGram, hg, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hOi, hOti]
  simp only [inverseGram, Matrix.mul_assoc]

theorem conjugate_first_diagonal {s : ℕ} (H O : Matrix (Fin (s + 1)) (Fin (s + 1)) ℝ)
    (u : Fin (s + 1) → ℝ) (hu : (fun i => O i 0) = u) :
    (Oᵀ * H * O) 0 0 = u ⬝ᵥ (H *ᵥ u) := by
  let e : Fin (s + 1) → ℝ := Pi.single 0 1
  have he : O *ᵥ e = u := by
    calc
      O *ᵥ e = fun i => O i 0 := by ext i; simp [e, Matrix.mulVec, dotProduct, Pi.single_apply]
      _ = u := hu
  have h := quadratic_coordinates O H e
  rw [he] at h
  simpa [e, Matrix.mulVec, dotProduct, Pi.single_apply] using h.symm

theorem iidMatrixLaw_inverseGram_unit_quadratic {d s : ℕ} (hs : s + 1 ≤ d)
    {v : NNReal} (hv : v ≠ 0) (u : Fin (s + 1) → ℝ) (hu : u ⬝ᵥ u = 1) :
    (iidMatrixLaw d (s + 1) v).map (fun X => u ⬝ᵥ (inverseGram X *ᵥ u)) =
      (squaredGaussianLaw (d - s) v).map (fun t : ℝ => t⁻¹) := by
  let O := eigenvectorGauge u
  have hO : Oᵀ * O = 1 := eigenvectorGauge_orthogonal u
  have hcol : (fun i => O i 0) = u := eigenvectorGauge_first_column u hu
  have hf : Measurable (fun X : Matrix (Fin d) (Fin (s + 1)) ℝ => inverseGram X 0 0) :=
    (measurable_pi_apply 0).comp ((measurable_pi_apply 0).comp (measurable_inverseGram d (s + 1)))
  have hrot : Measurable (fun X : Matrix (Fin d) (Fin (s + 1)) ℝ => X * O) :=
    (show Continuous (fun X : Matrix (Fin d) (Fin (s + 1)) ℝ => X * O) by fun_prop).measurable
  have he (X : Matrix (Fin d) (Fin (s + 1)) ℝ) :
      inverseGram (X * O) 0 0 = u ⬝ᵥ (inverseGram X *ᵥ u) := by
    rw [inverseGram_right_orthogonal X O hO, conjugate_first_diagonal _ O u hcol]
  calc
    _ = (iidMatrixLaw d (s + 1) v).map
        ((fun X => inverseGram X 0 0) ∘ (fun X => X * O)) := by
      congr 1
      funext X
      exact (he X).symm
    _ = ((iidMatrixLaw d (s + 1) v).map (fun X => X * O)).map (fun X => inverseGram X 0 0) :=
      (Measure.map_map hf hrot).symm
    _ = _ := by rw [iidMatrixLaw_right_orthogonal O hO, iidMatrixLaw_inverseGram_first hs hv]

end
end LowRank
