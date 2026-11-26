import Matvec.CoreAlgebra
import LowRank.MatrixNetBound
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! Continuity of the actual least stretch, and quantitative visible-block
perturbations used to obtain invertible pivots by arbitrarily small shifts. -/

namespace Matvec

noncomputable section
open Matrix
open scoped Matrix

section Continuity
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem leastStretch_sub_le (A B : E →L[ℝ] F) (hunit : ∃ x : E, ‖x‖ = 1) :
    leastStretch A - ‖A - B‖ ≤ leastStretch B := by
  apply le_csInf
  · obtain ⟨x, hx⟩ := hunit
    exact ⟨‖B x‖, x, hx, rfl⟩
  · rintro r ⟨x, hx, rfl⟩
    have ha := leastStretch_le_of_unit A hx
    have hd := (A - B).le_opNorm x
    rw [hx, mul_one, ContinuousLinearMap.sub_apply] at hd
    have ht := norm_le_norm_add_norm_sub (B x) (A x)
    rw [norm_sub_rev] at ht
    linarith

theorem leastStretch_lipschitz (A B : E →L[ℝ] F) (hunit : ∃ x : E, ‖x‖ = 1) :
    |leastStretch A - leastStretch B| ≤ ‖A - B‖ := by
  have hab := leastStretch_sub_le A B hunit
  have hba := leastStretch_sub_le B A hunit
  rw [norm_sub_rev B A] at hba
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem lipschitzWith_leastStretch (hunit : ∃ x : E, ‖x‖ = 1) :
    LipschitzWith 1 (leastStretch : (E →L[ℝ] F) → ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  simpa only [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul] using
    leastStretch_lipschitz A B hunit

theorem continuous_leastStretch (hunit : ∃ x : E, ‖x‖ = 1) :
    Continuous (leastStretch : (E →L[ℝ] F) → ℝ) :=
  (lipschitzWith_leastStretch hunit).continuous

end Continuity

theorem continuous_matrix_leastStretch (m n : ℕ) (hn : 0 < n) :
    Continuous (fun A : Matrix (Fin m) (Fin n) ℝ => leastStretch (LowRank.matrixEuclideanMap A)) := by
  have hunit : ∃ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 := by
    refine ⟨(EuclideanSpace.basisFun (Fin n) ℝ) ⟨0, hn⟩, ?_⟩
    exact (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one _
  exact (continuous_leastStretch hunit).comp (LowRank.continuous_matrixEuclideanMap m n)

theorem measurable_matrix_leastStretch (m n : ℕ) (hn : 0 < n) :
    Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => leastStretch (LowRank.matrixEuclideanMap A)) :=
  (continuous_matrix_leastStretch m n hn).measurable

/-- The visible-pivot perturbation diag(δI_q,0_k), on the actual Euclidean
sum-index space. -/
def visibleBlockShift (q k : ℕ) (δ : ℝ) :
    EuclideanSpace ℝ (Fin q ⊕ Fin k) →L[ℝ] EuclideanSpace ℝ (Fin q ⊕ Fin k) :=
  LinearMap.toContinuousLinearMap
    (Matrix.toEuclideanLin (Matrix.fromBlocks (δ • (1 : Matrix (Fin q) (Fin q) ℝ))
      (0 : Matrix (Fin q) (Fin k) ℝ) (0 : Matrix (Fin k) (Fin q) ℝ) 0))

theorem visibleBlockShift_norm_le (q k : ℕ) (δ : ℝ) : ‖visibleBlockShift q k δ‖ ≤ |δ| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg δ)
  intro x
  have hnorm (y : EuclideanSpace ℝ (Fin q ⊕ Fin k)) :
      ‖y‖ ^ 2 = ∑ i, (y i) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    simp only [Real.norm_eq_abs, sq_abs]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (abs_nonneg δ) (norm_nonneg x))).mp
  rw [mul_pow, sq_abs, hnorm, hnorm]
  change (∑ i, ((Matrix.fromBlocks (δ • (1 : Matrix (Fin q) (Fin q) ℝ))
    (0 : Matrix (Fin q) (Fin k) ℝ) (0 : Matrix (Fin k) (Fin q) ℝ) 0) *ᵥ
      (x : Fin q ⊕ Fin k → ℝ)) i ^ 2) ≤ δ ^ 2 * ∑ i, x i ^ 2
  simp only [Matrix.fromBlocks_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
    Matrix.zero_mulVec, add_zero, zero_add, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
    Pi.zero_apply, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero,
    mul_pow, ← Finset.mul_sum]
  have hnonneg : 0 ≤ δ ^ 2 * ∑ i : Fin k, x (Sum.inr i) ^ 2 := by positivity
  nlinarith

/-- Orthogonal changes of source and target coordinates preserve the bound
on a visible-block perturbation. -/
theorem isometry_conjugate_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : E →L[ℝ] E) (U V : E ≃ₗᵢ[ℝ] E) (δ : ℝ) (hP : ‖P‖ ≤ |δ|) :
    ‖U.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (P.comp V.toContinuousLinearEquiv.toContinuousLinearMap)‖ ≤ |δ| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg δ)
  intro x
  change ‖U (P (V x))‖ ≤ |δ| * ‖x‖
  rw [U.norm_map]
  have h := P.le_of_opNorm_le hP (V x)
  simpa only [V.norm_map] using h

end
end Matvec
