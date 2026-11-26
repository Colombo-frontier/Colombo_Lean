import LowRank.GramInverseDistance
import LowRank.GaussianProjectionSquaredLaw

/-! The inverse Gram diagonal of a full-column-rank Gaussian matrix has
the reciprocal squared-Gaussian law in its residual dimension. The other
columns are random; their conditioning is handled by a product-law proof. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

def inverseGram {d s : ℕ} (X : Matrix (Fin d) (Fin s) ℝ) : Matrix (Fin s) (Fin s) ℝ :=
  (Xᵀ * X)⁻¹

theorem measurable_inverseGram (d s : ℕ) :
    Measurable (inverseGram : Matrix (Fin d) (Fin s) ℝ → _) :=
  measurable_real_matrix_inverse.comp (show Continuous (fun X : Matrix (Fin d) (Fin s) ℝ => Xᵀ * X) by fun_prop).measurable

def firstColumnResidualSq {d s : ℕ} (X : Matrix (Fin d) (Fin (s + 1)) ℝ) : ℝ :=
  (fun i => X i 0) ⬝ᵥ (leftKernelProjector (X.submatrix id Fin.succ) *ᵥ (fun i => X i 0))

theorem measurable_kernel_quadratic_pair (d s : ℕ) :
    Measurable (fun p : Matrix (Fin d) (Fin s) ℝ × (Fin d → ℝ) =>
      p.2 ⬝ᵥ (leftKernelProjector p.1 *ᵥ p.2)) := by
  have hP : Measurable (fun p : Matrix (Fin d) (Fin s) ℝ × (Fin d → ℝ) => leftKernelProjector p.1) :=
    (measurable_leftKernelProjector (m := Fin d) (n := Fin s)).comp measurable_fst
  simp only [dotProduct, Matrix.mulVec]
  fun_prop

theorem measurable_firstColumnResidualSq (d s : ℕ) :
    Measurable (firstColumnResidualSq : Matrix (Fin d) (Fin (s + 1)) ℝ → ℝ) := by
  have hm : Measurable (fun X : Matrix (Fin d) (Fin (s + 1)) ℝ =>
      (X.submatrix id Fin.succ, fun i => X i 0)) := by fun_prop
  exact (measurable_kernel_quadratic_pair d s).comp hm

theorem iidMatrixLaw_firstColumnResidualSq {d s : ℕ} (hs : s ≤ d) {v : NNReal} (hv : v ≠ 0) :
    (iidMatrixLaw d (s + 1) v).map firstColumnResidualSq = squaredGaussianLaw (d - s) v := by
  let f := fun p : Matrix (Fin d) (Fin s) ℝ × (Fin d → ℝ) =>
    p.2 ⬝ᵥ (leftKernelProjector p.1 *ᵥ p.2)
  have hF : MeasurePreserving (fun p => (p.1, f p))
      ((iidMatrixLaw d s v).prod (iidVectorLaw d v))
      ((iidMatrixLaw d s v).prod (squaredGaussianLaw (d - s) v)) := by
    apply (MeasurePreserving.id (iidMatrixLaw d s v)).skew_product
      (g := fun Y x => x ⬝ᵥ (leftKernelProjector Y *ᵥ x)) (measurable_kernel_quadratic_pair d s)
    filter_upwards [iidMatrixLaw_mulVec_injective_ae d s hs hv] with Y hY
    exact iidVectorLaw_kernel_quadratic Y hY hs v
  have hpres := hF.comp (Measure.measurePreserving_swap.comp (splitFirstColumn_preserving d s v))
  have h := congrArg (Measure.map Prod.snd) hpres.map_eq
  rw [Measure.map_map measurable_snd hpres.measurable, Measure.map_snd_prod] at h
  simpa only [measure_univ, one_smul, Function.comp_def, f, splitFirstColumn, firstColumnResidualSq,
    Matrix.submatrix, id_eq] using h

theorem inverseGram_first_eq_residual {d s : ℕ} (X : Matrix (Fin d) (Fin (s + 1)) ℝ)
    (hX : Function.Injective X.mulVec) : inverseGram X 0 0 = (firstColumnResidualSq X)⁻¹ := by
  have heq : prependColumn (fun i => X i 0) (X.submatrix id Fin.succ) = X := by
    ext i j
    refine Fin.cases ?_ (fun j => ?_) j <;> rfl
  have hinj : Function.Injective (prependColumn (fun i => X i 0) (X.submatrix id Fin.succ)).mulVec := by
    rw [heq]
    exact hX
  simpa only [heq, inverseGram, firstColumnResidualSq] using
    gram_inverse_first_distance (fun i => X i 0) (X.submatrix id Fin.succ) hinj

theorem iidMatrixLaw_inverseGram_first {d s : ℕ} (hs : s + 1 ≤ d) {v : NNReal} (hv : v ≠ 0) :
    (iidMatrixLaw d (s + 1) v).map (fun X => inverseGram X 0 0) =
      (squaredGaussianLaw (d - s) v).map (fun t : ℝ => t⁻¹) := by
  have heq : (fun X : Matrix (Fin d) (Fin (s + 1)) ℝ => inverseGram X 0 0) =ᵐ[iidMatrixLaw d (s + 1) v]
      (fun X => (firstColumnResidualSq X)⁻¹) := by
    filter_upwards [iidMatrixLaw_mulVec_injective_ae d (s + 1) hs hv] with X hX
    exact inverseGram_first_eq_residual X hX
  rw [Measure.map_congr heq]
  change (iidMatrixLaw d (s + 1) v).map ((fun t : ℝ => t⁻¹) ∘ firstColumnResidualSq) = _
  rw [← Measure.map_map measurable_inv (measurable_firstColumnResidualSq d s),
    iidMatrixLaw_firstColumnResidualSq (by omega) hv]

end
end LowRank
