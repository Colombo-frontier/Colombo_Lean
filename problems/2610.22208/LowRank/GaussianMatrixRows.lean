import LowRank.GaussianCoordinates
import LowRank.GaussianAdaptiveRotation

/-! Actual iid rectangular Gaussian matrices: rowwise orthogonal invariance
and independence of the first column and the remaining columns. The variance
is independent of the changing block dimensions. -/

namespace LowRank
open MeasureTheory ProbabilityTheory
noncomputable section

def iidMatrixLaw (r s : ℕ) (v : NNReal) : Measure (Matrix (Fin r) (Fin s) ℝ) :=
  Measure.pi (fun _ : Fin r => iidVectorLaw s v)

instance iidMatrixLaw_probability (r s : ℕ) (v : NNReal) :
    IsProbabilityMeasure (iidMatrixLaw r s v) :=
  Measure.pi.instIsProbabilityMeasure _

theorem gaussianMatrixLaw_eq_iidMatrixLaw (d s : ℕ) :
    gaussianMatrixLaw d s = iidMatrixLaw d s (d : NNReal)⁻¹ := rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {r s : ℕ}

def rotateMatrixRows (b : OrthonormalBasis (Fin s) ℝ E) (e : E ≃ₗᵢ[ℝ] E)
    (X : Matrix (Fin r) (Fin s) ℝ) : Matrix (Fin r) (Fin s) ℝ :=
  fun i => coordinateRotation b e (X i)

theorem rotateMatrixRows_apply (b : OrthonormalBasis (Fin s) ℝ E) (e : E ≃ₗᵢ[ℝ] E)
    (X : Matrix (Fin r) (Fin s) ℝ) (i : Fin r) :
    rotateMatrixRows b e X i = basisCoordinates b (e ((basisCoordinates b).symm (X i))) := rfl

theorem rotateMatrixRows_preserving (b : OrthonormalBasis (Fin s) ℝ E)
    (e : E ≃ₗᵢ[ℝ] E) (v : NNReal) :
    MeasurePreserving (rotateMatrixRows (r := r) b e) (iidMatrixLaw r s v) (iidMatrixLaw r s v) := by
  exact measurePreserving_pi (fun _ : Fin r => iidVectorLaw s v) (fun _ => iidVectorLaw s v)
    (fun _ => ⟨(coordinateRotation b e).continuous.measurable, iidVectorLaw_coordinateRotation b e v⟩)

theorem state_dependent_matrix_rotation {S : Type*} [MeasurableSpace S]
    {ν : Measure S} [SFinite ν] (b : OrthonormalBasis (Fin s) ℝ E)
    (e : S → E ≃ₗᵢ[ℝ] E) (v : NNReal)
    (he : Measurable (fun p : S × Matrix (Fin r) (Fin s) ℝ => rotateMatrixRows b (e p.1) p.2)) :
    (ν.prod (iidMatrixLaw r s v)).map
      (fun p => (p.1, rotateMatrixRows b (e p.1) p.2)) = ν.prod (iidMatrixLaw r s v) := by
  exact ((MeasurePreserving.id ν).skew_product he
    (Filter.Eventually.of_forall (fun z => (rotateMatrixRows_preserving b (e z) v).map_eq))).map_eq

def splitFirstCoordinate (z : Fin (s + 1) → ℝ) : ℝ × (Fin s → ℝ) :=
  (z 0, fun j => z j.succ)

theorem splitFirstCoordinate_preserving (s : ℕ) (v : NNReal) :
    MeasurePreserving (splitFirstCoordinate (s := s)) (iidVectorLaw (s + 1) v)
      ((gaussianReal 0 v).prod (iidVectorLaw s v)) := by
  have h := measurePreserving_piFinSuccAbove (fun _ : Fin (s + 1) => gaussianReal 0 v) 0
  simpa only [MeasurableEquiv.piFinSuccAbove, Equiv.piSplitAt,
    Fin.succAbove_zero] using h

def splitFirstColumn (X : Matrix (Fin r) (Fin (s + 1)) ℝ) :
    (Fin r → ℝ) × Matrix (Fin r) (Fin s) ℝ :=
  (fun i => X i 0, fun i j => X i j.succ)

theorem splitFirstColumn_preserving (r s : ℕ) (v : NNReal) :
    MeasurePreserving (splitFirstColumn (r := r) (s := s)) (iidMatrixLaw r (s + 1) v)
      ((iidVectorLaw r v).prod (iidMatrixLaw r s v)) := by
  have hrows := measurePreserving_pi (fun _ : Fin r => iidVectorLaw (s + 1) v)
    (fun _ => (gaussianReal 0 v).prod (iidVectorLaw s v))
    (fun _ => splitFirstCoordinate_preserving s v)
  have hcols := measurePreserving_arrowProdEquivProdArrow ℝ (Fin s → ℝ) (Fin r)
    (fun _ => gaussianReal 0 v) (fun _ => iidVectorLaw s v)
  exact hcols.comp hrows

def splitFirstRow (X : Matrix (Fin (r + 1)) (Fin s) ℝ) :
    (Fin s → ℝ) × Matrix (Fin r) (Fin s) ℝ :=
  (X 0, fun i => X i.succ)

theorem splitFirstRow_preserving (r s : ℕ) (v : NNReal) :
    MeasurePreserving (splitFirstRow (r := r) (s := s)) (iidMatrixLaw (r + 1) s v)
      ((iidVectorLaw s v).prod (iidMatrixLaw r s v)) := by
  have h := measurePreserving_piFinSuccAbove (fun _ : Fin (r + 1) => iidVectorLaw s v) 0
  simpa only [MeasurableEquiv.piFinSuccAbove, Equiv.piSplitAt,
    Fin.succAbove_zero] using h

end
end LowRank
