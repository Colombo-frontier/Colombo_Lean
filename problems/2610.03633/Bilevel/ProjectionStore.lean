import Bilevel.ProjectionNormalization

/-! A finite Borel representation of the adaptively changing projection subspace. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace BigOperators
namespace Bilevel.ProjectionStore
open EuclideanGaussian ProjectionGeometry

abbrev Store (d : ℕ) := Fin d → Space d
def basis (d : ℕ) := EuclideanSpace.basisFun (Fin d) ℝ
def ofSubspace (d : ℕ) (V : Submodule ℝ (Space d)) : Store d := fun i => project V (basis d i)
def apply (d : ℕ) (A : Store d) (q : Space d) : Space d := ∑ i, ⟪basis d i,q⟫ • A i
def residual (d : ℕ) (A : Store d) (q : Space d) : Space d := q-apply d A q
def direction (d : ℕ) (A : Store d) (q : Space d) : Space d := ‖residual d A q‖⁻¹ • residual d A q
def insert (d : ℕ) (A : Store d) (q : Space d) : Store d :=
  fun i => A i + ⟪direction d A q,basis d i⟫ • direction d A q

theorem apply_subspace (d : ℕ) (V : Submodule ℝ (Space d)) (q : Space d) :
    apply d (ofSubspace d V) q = project V q := by
  let L := V.subtypeL.comp V.orthogonalProjection
  have h : apply d (ofSubspace d V) q = L (∑ i, ⟪basis d i,q⟫ • basis d i) := by
    rw [map_sum]
    simp only [map_smul,apply,ofSubspace]
    rfl
  rw [(basis d).sum_repr' q] at h
  exact h

theorem residual_subspace (d : ℕ) (V : Submodule ℝ (Space d)) (q : Space d) :
    residual d (ofSubspace d V) q = ProjectionGeometry.residual V q := by
  simp only [residual,apply_subspace,ProjectionGeometry.residual]

theorem direction_subspace (d : ℕ) (V : Submodule ℝ (Space d)) (q : Space d) :
    direction d (ofSubspace d V) q = revelationDirection V q := by
  simp only [direction,residual_subspace,revelationDirection]

theorem insert_subspace (d : ℕ) (V : Submodule ℝ (Space d)) (q : Space d) :
    insert d (ofSubspace d V) q = ofSubspace d (V ⊔ Submodule.span ℝ {q}) := by
  by_cases hq : ProjectionGeometry.residual V q = 0
  · rw [ProjectionNormalization.unchanged d V q hq]
    funext i
    simp [insert,direction_subspace,revelationDirection,hq]
  · have hs := ProjectionNormalization.span_eq d V q hq
    funext i
    change project V (basis d i) + ⟪direction d (ofSubspace d V) q,basis d i⟫ • direction d (ofSubspace d V) q = _
    rw [direction_subspace]
    change _ = project (V ⊔ Submodule.span ℝ {q}) (basis d i)
    rw [hs]
    exact (ProjectionObservation.query_projection d V _ (basis d i)
      (ProjectionNormalization.direction_mem d V q) (ProjectionNormalization.direction_norm d V q hq)).symm

variable {Ω : Type*} [MeasurableSpace Ω]

theorem apply_measurable (d : ℕ) (A : Ω → Store d) (hA : Measurable A)
    (q : Ω → Space d) (hq : Measurable q) : Measurable (fun ω => apply d (A ω) (q ω)) := by
  apply Finset.measurable_sum
  intro i _
  exact ((continuous_const.inner continuous_id).measurable.comp hq).smul ((measurable_pi_apply i).comp hA)

theorem residual_measurable (d : ℕ) (A : Ω → Store d) (hA : Measurable A)
    (q : Ω → Space d) (hq : Measurable q) : Measurable (fun ω => residual d (A ω) (q ω)) :=
  hq.sub (apply_measurable d A hA q hq)

theorem direction_measurable (d : ℕ) (A : Ω → Store d) (hA : Measurable A)
    (q : Ω → Space d) (hq : Measurable q) : Measurable (fun ω => direction d (A ω) (q ω)) :=
  ((residual_measurable d A hA q hq).norm.inv).smul (residual_measurable d A hA q hq)

theorem insert_measurable (d : ℕ) (A : Ω → Store d) (hA : Measurable A)
    (q : Ω → Space d) (hq : Measurable q) : Measurable (fun ω => insert d (A ω) (q ω)) := by
  apply measurable_pi_lambda
  intro i
  have hw := direction_measurable d A hA q hq
  exact ((measurable_pi_apply i).comp hA).add (((continuous_id.inner continuous_const).measurable.comp hw).smul hw)

end Bilevel.ProjectionStore
