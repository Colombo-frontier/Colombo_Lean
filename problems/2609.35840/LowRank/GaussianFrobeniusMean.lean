import LowRank.GaussianRightInverseTail
import LowRank.GaussianMomentArithmetic

/-! Exact first Frobenius moments of a deterministic linear image of the
Gaussian starting matrix. The result depends on the image, not on the
ambient dimension in which the random matrix was sampled. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators ENNReal
noncomputable section

theorem iidVectorLaw_quadratic_mean {d : ℕ} {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosSemidef) :
    (∫⁻ x, ENNReal.ofReal (x ⬝ᵥ (H *ᵥ x)) ∂iidVectorLaw d 1) = ENNReal.ofReal H.trace := by
  let sp := orderedMatrixSpectrum hH.isHermitian
  have hm : Measurable (fun x : Fin d → ℝ => sp.basis *ᵥ x) := by
    apply measurable_pi_lambda
    intro j
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have hf : Measurable (fun x : Fin d → ℝ => ENNReal.ofReal (x ⬝ᵥ (H *ᵥ x))) := by
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  have hrot : (iidVectorLaw d 1).map (fun x => sp.basis *ᵥ x) = iidVectorLaw d 1 := by
    simpa only [Matrix.transpose_transpose] using iidVectorLaw_orthogonal_compression sp.basisᵀ
      (by simpa only [Matrix.transpose_transpose] using sp.orthogonal_right) 1
  have hint := lintegral_map (μ := iidVectorLaw d 1) hf hm
  rw [hrot] at hint
  rw [hint]
  simp_rw [sp.quadratic, ENNReal.ofReal_sum_of_nonneg
    (fun i _ => mul_nonneg (sp.value_nonneg hH i) (sq_nonneg _)),
    ENNReal.ofReal_mul (sp.value_nonneg hH _)]
  rw [lintegral_finset_sum _ (fun i _ => by fun_prop)]
  have hi (i : Fin d) : (∫⁻ x, ENNReal.ofReal (x i ^ 2) ∂iidVectorLaw d 1) = 1 := by
    have h := iidVectorLaw_coordinate_square_moment i (a := 1) (by norm_num)
    simpa only [Real.rpow_one, gaussianMomentFormula_one (by omega : 0 < 1), Nat.cast_one,
      ENNReal.ofReal_one] using h
  have hterm (i : Fin d) : (∫⁻ x, ENNReal.ofReal (sp.value i) * ENNReal.ofReal (x i ^ 2)
      ∂iidVectorLaw d 1) = ENNReal.ofReal (sp.value i) := by
    rw [lintegral_const_mul _ (by fun_prop), hi, mul_one]
  simp_rw [hterm]
  rw [sp.trace, ENNReal.ofReal_sum_of_nonneg (fun i _ => sp.value_nonneg hH i)]

theorem iidMatrixLaw_column_preserving {r s : ℕ} (j : Fin s) (v : NNReal) :
    MeasurePreserving (fun U : Matrix (Fin r) (Fin s) ℝ => fun i => U i j)
      (iidMatrixLaw r s v) (iidVectorLaw r v) := by
  cases s with
  | zero => exact Fin.elim0 j
  | succ s =>
    have hsplit := measurePreserving_piFinSuccAbove (fun _ : Fin (s + 1) => iidVectorLaw r v) j
    have hfst : MeasurePreserving
        (Prod.fst : (Fin r → ℝ) × Matrix (Fin s) (Fin r) ℝ → (Fin r → ℝ))
        ((iidVectorLaw r v).prod (iidMatrixLaw s r v)) (iidVectorLaw r v) :=
      ⟨measurable_fst, by rw [Measure.map_fst_prod, measure_univ, one_smul]⟩
    exact (hfst.comp hsplit).comp (iidMatrixLaw_transpose_preserving r (s + 1) v)

theorem frobeniusSq_mul_eq_sum_quadratic {a d s : ℕ}
    (M : Matrix (Fin a) (Fin d) ℝ) (U : Matrix (Fin d) (Fin s) ℝ) :
    frobeniusSq (M * U) = ∑ j, (fun i => U i j) ⬝ᵥ ((Mᵀ * M) *ᵥ (fun i => U i j)) := by
  rw [frobeniusSq, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have h := quadratic_coordinates M (1 : Matrix (Fin a) (Fin a) ℝ) (fun i => U i j)
  rw [Matrix.one_mulVec, Matrix.mul_one] at h
  simpa only [Matrix.one_mulVec, Matrix.mul_one, dotProduct, Matrix.mulVec, Matrix.mul_apply,
    pow_two] using h

theorem iidMatrixLaw_mul_frobeniusSq_mean {a d s : ℕ} (M : Matrix (Fin a) (Fin d) ℝ) :
    (∫⁻ U, ENNReal.ofReal (frobeniusSq (M * U)) ∂iidMatrixLaw d s 1) =
      ENNReal.ofReal ((s : ℝ) * frobeniusSq M) := by
  have hH : (Mᵀ * M).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_conjTranspose_mul_self M
  have hn (x : Fin d → ℝ) : 0 ≤ x ⬝ᵥ ((Mᵀ * M) *ᵥ x) := by simpa using hH.2 x
  have hf : Measurable (fun x : Fin d → ℝ => ENNReal.ofReal (x ⬝ᵥ ((Mᵀ * M) *ᵥ x))) := by
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  have hi (j : Fin s) :
      (∫⁻ U : Matrix (Fin d) (Fin s) ℝ,
        ENNReal.ofReal ((fun i => U i j) ⬝ᵥ ((Mᵀ * M) *ᵥ (fun i => U i j))) ∂iidMatrixLaw d s 1) =
          ENNReal.ofReal (frobeniusSq M) := by
    rw [← lintegral_map hf (iidMatrixLaw_column_preserving j 1).measurable,
      (iidMatrixLaw_column_preserving j 1).map_eq, iidVectorLaw_quadratic_mean hH,
      ← frobeniusSq_eq_trace_right]
  simp_rw [frobeniusSq_mul_eq_sum_quadratic,
    ENNReal.ofReal_sum_of_nonneg (fun j _ => hn _)]
  rw [lintegral_finset_sum _ (fun j _ => by
    simp only [dotProduct, Matrix.mulVec]
    fun_prop)]
  simp_rw [hi]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ENNReal.ofReal_mul (Nat.cast_nonneg s), ENNReal.ofReal_natCast]

theorem iidMatrixLaw_mul_frobeniusSq_tail_le {a d s : ℕ} (M : Matrix (Fin a) (Fin d) ℝ)
    {R : ℝ} (hR : 0 < R) :
    (iidMatrixLaw d s 1) {U | R < frobeniusSq (M * U)} ≤
      ENNReal.ofReal ((s : ℝ) * frobeniusSq M) / ENNReal.ofReal R := by
  have h := measure_frobeniusSq_tail_le (iidMatrixLaw d s 1) (fun U => M * U)
    (by fun_prop : Continuous (fun U : Matrix (Fin d) (Fin s) ℝ => M * U)).measurable hR
  rwa [iidMatrixLaw_mul_frobeniusSq_mean] at h

end
end LowRank
