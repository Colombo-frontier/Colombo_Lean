import LowRank.GaussianMatrixTranspose
import LowRank.GaussianReveal

/-! Left orthogonal rotations of actual iid matrices, including a jointly
measurable Householder rotation chosen from the prior state. -/

namespace LowRank
open MeasureTheory
open scoped Matrix
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {r s : ℕ}

def rotateMatrixColumns (b : OrthonormalBasis (Fin r) ℝ E) (e : E ≃ₗᵢ[ℝ] E)
    (X : Matrix (Fin r) (Fin s) ℝ) : Matrix (Fin r) (Fin s) ℝ :=
  (rotateMatrixRows b e Xᵀ)ᵀ

theorem rotateMatrixColumns_apply (b : OrthonormalBasis (Fin r) ℝ E) (e : E ≃ₗᵢ[ℝ] E)
    (X : Matrix (Fin r) (Fin s) ℝ) (i : Fin r) (j : Fin s) :
    rotateMatrixColumns b e X i j = coordinateRotation b e (fun k => X k j) i := rfl

theorem rotateMatrixColumns_preserving (b : OrthonormalBasis (Fin r) ℝ E)
    (e : E ≃ₗᵢ[ℝ] E) (v : NNReal) :
    MeasurePreserving (rotateMatrixColumns (s := s) b e) (iidMatrixLaw r s v)
      (iidMatrixLaw r s v) := by
  exact (iidMatrixLaw_transpose_preserving s r v).comp
    ((rotateMatrixRows_preserving (r := s) b e v).comp (iidMatrixLaw_transpose_preserving r s v))

theorem measurable_query_rotation {S : Type*} [MeasurableSpace S]
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E) (q : S → Fin (r + 1) → ℝ)
    (hq : Measurable q) :
    Measurable (fun p : S × Matrix (Fin (r + 1)) (Fin s) ℝ =>
      rotateMatrixColumns b (rowGauge b (q p.1)) p.2) := by
  have htrans : Measurable (Matrix.transpose : Matrix (Fin (r + 1)) (Fin s) ℝ → _) := by
    fun_prop
  have harg : Measurable (fun p : S × Matrix (Fin (r + 1)) (Fin s) ℝ => (q p.1, p.2ᵀ)) :=
    (hq.comp measurable_fst).prodMk (htrans.comp measurable_snd)
  have hrot := (measurable_rowGauge_rotation (r := s) b).comp harg
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact (measurable_pi_apply i).comp ((measurable_pi_apply j).comp hrot)

/-- Queries may depend on all of the prior exposed state, while the matrix
block starts independent of that state. -/
theorem query_rotation_preserving {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [SFinite ν] (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (q : S → Fin (r + 1) → ℝ) (hq : Measurable q) (v : NNReal) :
    MeasurePreserving
      (fun p : S × Matrix (Fin (r + 1)) (Fin s) ℝ =>
        (p.1, rotateMatrixColumns b (rowGauge b (q p.1)) p.2))
      (ν.prod (iidMatrixLaw (r + 1) s v)) (ν.prod (iidMatrixLaw (r + 1) s v)) := by
  exact (MeasurePreserving.id ν).skew_product (measurable_query_rotation b q hq)
    (Filter.Eventually.of_forall (fun z => (rotateMatrixColumns_preserving b
      (rowGauge b (q z)) v).map_eq))

end
end LowRank
