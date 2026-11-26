import NCBall.GaussianOrthogonal
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-! # Measurable projection updates for an arbitrary scalar query -/

noncomputable section
open MeasureTheory ProbabilityTheory Submodule
open scoped InnerProductSpace
namespace NCBall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

@[fun_prop]
theorem measurable_clm_eval {A : Type*} [MeasurableSpace A]
    {Q : A → E →L[ℝ] E} {x : A → E} (hQ : Measurable Q) (hx : Measurable x) :
    Measurable (fun s => Q s (x s)) :=
  (show Continuous (fun p : (E →L[ℝ] E) × E => p.1 p.2) from
    isBoundedBilinearMap_apply.continuous).measurable.comp (hQ.prodMk hx)

def rankProjection (b : E) : E →L[ℝ] E :=
  (ℝ ∙ b).subtypeL.comp (ℝ ∙ b).orthogonalProjection

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem rankProjection_apply (b x : E) :
    rankProjection b x = (⟪b, x⟫_ℝ / ‖b‖ ^ 2) • b :=
  Submodule.orthogonalProjection_singleton ℝ x

theorem rankProjection_measurable : Measurable (rankProjection : E → E →L[ℝ] E) := by
  have he : rankProjection = fun b : E => (‖b‖ ^ 2)⁻¹ • (innerSL ℝ b).smulRight b := by
    funext b
    ext x
    simp only [rankProjection_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply, smul_smul]
    congr 1
    ring
  rw [he]
  have hs : Continuous (fun b : E => (innerSL ℝ b).smulRight b) :=
    (ContinuousLinearMap.smulRightL ℝ E E).continuous₂.comp
      ((innerSL ℝ).continuous.prodMk continuous_id)
  exact ((continuous_norm.pow 2).measurable.inv).smul hs.measurable

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem rankProjection_self (b : E) : rankProjection b b = b := by
  exact (Submodule.orthogonalProjection_eq_self_iff (K := ℝ ∙ b)).mpr
    (Submodule.mem_span_singleton_self b)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem rankProjection_idempotent (b x : E) :
    rankProjection b (rankProjection b x) = rankProjection b x := by
  exact (Submodule.orthogonalProjection_eq_self_iff (K := ℝ ∙ b)).mpr
    ((ℝ ∙ b).orthogonalProjection x).property

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem rankProjection_symmetric (b x y : E) :
    ⟪rankProjection b x, y⟫_ℝ = ⟪x, rankProjection b y⟫_ℝ :=
  Submodule.inner_orthogonalProjection_left_eq_right _ _ _

def IsResidualProjection (Q : E →L[ℝ] E) : Prop :=
  (∀ x, Q (Q x) = Q x) ∧ (∀ x y, ⟪Q x, y⟫_ℝ = ⟪x, Q y⟫_ℝ)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem isResidualProjection_id : IsResidualProjection (ContinuousLinearMap.id ℝ E) := by
  constructor <;> intros <;> rfl

def residualUpdate (Q : E →L[ℝ] E) (a : E) : E →L[ℝ] E := Q - rankProjection (Q a)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem projection_update_commutes {Q : E →L[ℝ] E} (hQ : IsResidualProjection Q) (a x : E) :
    Q (rankProjection (Q a) x) = rankProjection (Q a) x ∧
      rankProjection (Q a) (Q x) = rankProjection (Q a) x := by
  constructor
  · rw [rankProjection_apply, map_smul, hQ.1]
  · simp only [rankProjection_apply]
    rw [← hQ.2, hQ.1]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem residualUpdate_isProjection {Q : E →L[ℝ] E} (hQ : IsResidualProjection Q) (a : E) :
    IsResidualProjection (residualUpdate Q a) := by
  constructor
  · intro x
    simp only [residualUpdate, ContinuousLinearMap.sub_apply, map_sub,
      (projection_update_commutes hQ a x).1, (projection_update_commutes hQ a x).2,
      hQ.1, rankProjection_idempotent]
    abel
  · intro x y
    simp only [residualUpdate, ContinuousLinearMap.sub_apply, inner_sub_left,
      inner_sub_right, hQ.2, rankProjection_symmetric]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem residualUpdate_query_zero {Q : E →L[ℝ] E} (hQ : IsResidualProjection Q) (a x : E) :
    ⟪a, residualUpdate Q a x⟫_ℝ = 0 := by
  simp only [residualUpdate, ContinuousLinearMap.sub_apply, inner_sub_right]
  rw [← hQ.2, ← rankProjection_symmetric]
  have hfix : rankProjection (Q a) a = Q a := by
    rw [← (projection_update_commutes hQ a a).2, rankProjection_self]
  rw [hfix, sub_self]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem residualUpdate_recombine {Q : E →L[ℝ] E} (hQ : IsResidualProjection Q) (a z w : E) :
    Q (rankProjection (Q a) z + (w - rankProjection (Q a) w)) =
      rankProjection (Q a) z + residualUpdate Q a w := by
  simp only [map_add, map_sub, (projection_update_commutes hQ a z).1,
    (projection_update_commutes hQ a w).1, residualUpdate, ContinuousLinearMap.sub_apply]

theorem residualUpdate_measurable :
    Measurable (fun p : (E →L[ℝ] E) × E => residualUpdate p.1 p.2) := by
  unfold residualUpdate
  exact measurable_fst.sub (rankProjection_measurable.comp (by fun_prop))

end NCBall
