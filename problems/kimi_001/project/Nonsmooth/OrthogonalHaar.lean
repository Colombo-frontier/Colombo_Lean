import Nonsmooth.Basic
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Measure.Haar.Basic

open MeasureTheory Metric Filter Function
open scoped Topology InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

abbrev OrthogonalTransform (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] := unitary (E →L[ℝ] E)

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

instance orthogonalTransformTopologicalGroup : IsTopologicalGroup (OrthogonalTransform E) where
  continuous_mul := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  continuous_inv := by
    apply Continuous.subtype_mk
    exact continuous_star.comp continuous_subtype_val

theorem orthogonalTransform_isCompact : IsCompact (unitary (E →L[ℝ] E) : Set (E →L[ℝ] E)) := by
  have hc : IsClosed (unitary (E →L[ℝ] E) : Set (E →L[ℝ] E)) :=
    (isClosed_eq (continuous_star.mul continuous_id) continuous_const).inter
      (isClosed_eq (continuous_id.mul continuous_star) continuous_const)
  apply (isCompact_closedBall (0 : E →L[ℝ] E) 1).of_isClosed_subset hc
  intro U hU
  rw [mem_closedBall, dist_zero_right, CStarRing.norm_of_mem_unitary hU]

instance orthogonalTransformCompactSpace : CompactSpace (OrthogonalTransform E) :=
  isCompact_iff_compactSpace.mp orthogonalTransform_isCompact

instance orthogonalTransformMeasurableSpace : MeasurableSpace (OrthogonalTransform E) :=
  borel (OrthogonalTransform E)

instance orthogonalTransformBorelSpace : BorelSpace (OrthogonalTransform E) := ⟨rfl⟩

def orthogonalPositiveCompact (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] : TopologicalSpace.PositiveCompacts (OrthogonalTransform E) :=
  ⟨⟨Set.univ, isCompact_univ⟩, by simpa only [interior_univ] using (Set.univ_nonempty : (Set.univ : Set (OrthogonalTransform E)).Nonempty)⟩

/-- A concrete Haar probability on the compact group of all orthogonal transformations. -/
def orthogonalHaar (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] : Measure (OrthogonalTransform E) :=
  Measure.haarMeasure (orthogonalPositiveCompact E)

instance orthogonalHaar_probability : IsProbabilityMeasure (orthogonalHaar E) := by
  constructor
  exact Measure.haarMeasure_self

instance orthogonalHaar_leftInvariant : (orthogonalHaar E).IsMulLeftInvariant := by
  unfold orthogonalHaar
  infer_instance

instance orthogonalHaar_rightInvariant : (orthogonalHaar E).IsMulRightInvariant where
  map_mul_right_eq_self Q := by
    apply Eq.symm
    apply (Measure.haarMeasure_eq_iff (orthogonalPositiveCompact E) _).mpr
    change (Measure.map (fun P : OrthogonalTransform E => P * Q) (orthogonalHaar E)) Set.univ = 1
    have hm : Measurable (fun P : OrthogonalTransform E => P * Q) :=
      (continuous_id.mul continuous_const).measurable
    rw [Measure.map_apply hm MeasurableSet.univ]
    simp

theorem orthogonalAction_continuous :
    Continuous (fun p : OrthogonalTransform E × E => (p.1.val : E →L[ℝ] E) p.2) :=
  (continuous_subtype_val.comp continuous_fst).clm_apply continuous_snd

theorem orthogonalHaar_integral_mul_right (Q : OrthogonalTransform E) (f : OrthogonalTransform E → ℝ) :
    (∫ P, f (P * Q) ∂orthogonalHaar E) = ∫ P, f P ∂orthogonalHaar E :=
  integral_mul_right_eq_self f Q

theorem orthogonalHaar_integral_mul_left (Q : OrthogonalTransform E) (f : OrthogonalTransform E → ℝ) :
    (∫ P, f (Q * P) ∂orthogonalHaar E) = ∫ P, f P ∂orthogonalHaar E :=
  integral_mul_left_eq_self f Q

end
end Nonsmooth
