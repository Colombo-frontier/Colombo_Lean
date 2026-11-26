-- Adapted from the standalone local StronglyConvex/OrthogonalHaar.lean module.
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.FunProp

/-!
# The normalized Haar probability on the finite orthogonal group

This file supplies the concrete compact probability space used for the
random rotations in the B and C rows.  The construction uses mathlib's
Haar measure on locally compact groups and normalizes its finite mass.
-/

namespace NCConcave16991.Haar

noncomputable section

open MeasureTheory Set

/-- The real orthogonal group in dimension `k`. -/
abbrev OrthogonalGroup (k : ℕ) := Matrix.orthogonalGroup (Fin k) ℝ

theorem isCompact_orthogonalGroup (k : ℕ) :
    IsCompact (Matrix.orthogonalGroup (Fin k) ℝ :
      Set (Matrix (Fin k) (Fin k) ℝ)) := by
  apply (isCompact_Icc.matrix).of_isClosed_subset isClosed_unitary
  intro U hU
  rw [Set.mem_matrix]
  intro i j
  have hij := entry_norm_bound_of_unitary hU i j
  simpa [Real.norm_eq_abs, abs_le] using hij

/-- Finite-dimensional orthogonal groups are compact. -/
noncomputable instance orthogonalGroupCompactSpace (k : ℕ) :
    CompactSpace (OrthogonalGroup k) :=
  isCompact_iff_compactSpace.mp (isCompact_orthogonalGroup k)

/-- We use the Borel measurable structure inherited from the matrix
topology. -/
noncomputable instance orthogonalGroupMeasurableSpace (k : ℕ) :
    MeasurableSpace (OrthogonalGroup k) := borel (OrthogonalGroup k)

instance orthogonalGroupBorelSpace (k : ℕ) :
    BorelSpace (OrthogonalGroup k) := ⟨rfl⟩

/-- The (unnormalized) Haar measure on the orthogonal group, packaged as a
finite measure using compactness. -/
def orthogonalHaarFinite (k : ℕ) : FiniteMeasure (OrthogonalGroup k) :=
  ⟨MeasureTheory.Measure.haar,
    inferInstanceAs (IsFiniteMeasure MeasureTheory.Measure.haar)⟩

/-- Normalized Haar probability on `O(k)`. -/
def orthogonalHaarProbability (k : ℕ) :
    ProbabilityMeasure (OrthogonalGroup k) :=
  (orthogonalHaarFinite k).normalize

theorem orthogonalHaarFinite_ne_zero (k : ℕ) :
    orthogonalHaarFinite k ≠ 0 := by
  intro hzero
  have hmeasure : (MeasureTheory.Measure.haar :
      Measure (OrthogonalGroup k)) = 0 := by
    simpa [orthogonalHaarFinite] using congrArg FiniteMeasure.toMeasure hzero
  have huniv : (MeasureTheory.Measure.haar :
      Measure (OrthogonalGroup k)) Set.univ ≠ 0 :=
    isOpen_univ.measure_ne_zero MeasureTheory.Measure.haar Set.univ_nonempty
  rw [hmeasure] at huniv
  simp at huniv

/-- The normalized Haar probability is the reciprocal-mass multiple of
the canonical Haar measure. -/
theorem orthogonalHaarProbability_toMeasure (k : ℕ) :
    ((orthogonalHaarProbability k :
      ProbabilityMeasure (OrthogonalGroup k)) : Measure (OrthogonalGroup k)) =
      (orthogonalHaarFinite k).mass⁻¹ • MeasureTheory.Measure.haar := by
  rw [orthogonalHaarProbability,
    (orthogonalHaarFinite k).toMeasure_normalize_eq_of_nonzero
      (orthogonalHaarFinite_ne_zero k)]
  rfl

/-- Normalized Haar probability remains left invariant. -/
theorem orthogonalHaarProbability_isMulLeftInvariant (k : ℕ) :
    Measure.IsMulLeftInvariant
      ((orthogonalHaarProbability k :
        ProbabilityMeasure (OrthogonalGroup k)) : Measure (OrthogonalGroup k)) := by
  rw [orthogonalHaarProbability_toMeasure]
  infer_instance

/-- An orthogonal matrix acts as a Euclidean linear isometry. -/
def orthogonalLinearIsometryEquiv {k : ℕ} (Q : OrthogonalGroup k) :
    EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k) :=
  Unitary.linearIsometryEquiv
    ⟨Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ) Q.1,
      Unitary.map_mem (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ)) Q.2⟩

@[simp]
theorem orthogonalLinearIsometryEquiv_apply {k : ℕ}
    (Q : OrthogonalGroup k) (y : EuclideanSpace ℝ (Fin k)) :
    orthogonalLinearIsometryEquiv Q y =
      Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ) Q.1 y := rfl

/-- Evaluation of an orthogonal matrix on a fixed vector varies
continuously with the matrix. -/
theorem continuous_orthogonalLinearIsometryEquiv_apply {k : ℕ}
    (y : EuclideanSpace ℝ (Fin k)) :
    Continuous (fun Q : OrthogonalGroup k =>
      orthogonalLinearIsometryEquiv Q y) := by
  change Continuous (fun Q : OrthogonalGroup k =>
    Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ) Q.1 y)
  change Continuous (fun Q : OrthogonalGroup k =>
    (WithLp.toLp 2 (Matrix.mulVec Q.1 (WithLp.ofLp y)) :
      EuclideanSpace ℝ (Fin k)))
  exact (PiLp.continuous_toLp (p := 2)
      (β := fun _ : Fin k => ℝ)).comp
    (continuous_subtype_val.matrix_mulVec continuous_const)

/-- Every one-coordinate threshold event for a Haar orthogonal matrix is
Borel measurable. -/
theorem measurableSet_orthogonal_coordinate_gt {k : ℕ}
    (y : EuclideanSpace ℝ (Fin k)) (i : Fin k) (a : ℝ) :
    MeasurableSet
      {Q : OrthogonalGroup k | |orthogonalLinearIsometryEquiv Q y i| > a} := by
  apply measurableSet_lt
  · fun_prop
  · exact ((PiLp.continuous_apply 2 _ i).comp
      (continuous_orthogonalLinearIsometryEquiv_apply y)).abs.measurable

end

end NCConcave16991.Haar

