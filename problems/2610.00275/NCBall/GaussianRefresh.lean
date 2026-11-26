import NCBall.ProjectionUpdate

/-! # Refreshing the unobserved Gaussian component after a scalar observation -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
namespace NCBall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def projectionRefresh (b : E) (zw : E × E) : E :=
  rankProjection b zw.1 + (zw.2 - rankProjection b zw.2)

theorem projectionRefresh_measurable :
    Measurable (fun p : E × (E × E) => projectionRefresh p.1 p.2) := by
  simp only [projectionRefresh, rankProjection_apply]
  fun_prop

theorem projectionRefresh_law (b : E) :
    ((euclideanGaussianLaw E).prod (euclideanGaussianLaw E)).map (projectionRefresh b) =
      euclideanGaussianLaw E := gaussian_orthogonal_recombine (ℝ ∙ b)

/-- The direction may be any measurable function of the already exposed state. -/
theorem adaptive_projectionRefresh_law {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [SFinite ν] (b : S → E) (hb : Measurable b) :
    (ν.prod ((euclideanGaussianLaw E).prod (euclideanGaussianLaw E))).map
      (fun p : S × (E × E) => (p.1, projectionRefresh (b p.1) p.2)) =
      ν.prod (euclideanGaussianLaw E) := by
  have hm : Measurable (fun p : S × (E × E) => projectionRefresh (b p.1) p.2) := by
    simp only [projectionRefresh, rankProjection_apply]
    fun_prop
  have hpoint : ∀ᵐ s ∂ν,
      ((euclideanGaussianLaw E).prod (euclideanGaussianLaw E)).map
        (fun zw : E × E => projectionRefresh (b s) zw) = euclideanGaussianLaw E :=
    Filter.Eventually.of_forall (fun s => projectionRefresh_law (b s))
  exact ((MeasurePreserving.id ν).skew_product
    (μc := (euclideanGaussianLaw E).prod (euclideanGaussianLaw E))
    (μd := euclideanGaussianLaw E)
    (g := fun (s : S) (zw : E × E) => projectionRefresh (b s) zw) hm hpoint).map_eq

def scalarReply (m : E) (Q : E →L[ℝ] E) (a z : E) : ℝ := ⟪a, m + Q z⟫_ℝ

def posteriorMeanUpdate (m : E) (Q : E →L[ℝ] E) (a : E) (y : ℝ) : E :=
  m + ((y - ⟪a, m⟫_ℝ) / ‖Q a‖ ^ 2) • Q a

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem posteriorMeanUpdate_reply (m : E) {Q : E →L[ℝ] E}
    (hQ : IsResidualProjection Q) (a z : E) :
    posteriorMeanUpdate m Q a (scalarReply m Q a z) = m + rankProjection (Q a) z := by
  simp only [posteriorMeanUpdate, scalarReply, inner_add_right, add_sub_cancel_left,
    ← hQ.2, rankProjection_apply]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem scalarReply_refresh (m : E) {Q : E →L[ℝ] E} (hQ : IsResidualProjection Q)
    (a z w : E) :
    scalarReply m Q a (projectionRefresh (Q a) (z, w)) = scalarReply m Q a z := by
  unfold scalarReply projectionRefresh
  rw [residualUpdate_recombine hQ]
  simp only [inner_add_right, residualUpdate_query_zero hQ, add_zero]
  rw [← rankProjection_symmetric]
  have hfix : rankProjection (Q a) a = Q a := by
    rw [← (projection_update_commutes hQ a a).2, rankProjection_self]
  rw [hfix, hQ.2]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem posterior_refresh_identity (m : E) {Q : E →L[ℝ] E} (hQ : IsResidualProjection Q)
    (a z w : E) :
    m + Q (projectionRefresh (Q a) (z, w)) =
      posteriorMeanUpdate m Q a (scalarReply m Q a z) + residualUpdate Q a w := by
  rw [posteriorMeanUpdate_reply m hQ]
  unfold projectionRefresh
  rw [residualUpdate_recombine hQ]
  abel

theorem scalarReply_measurable :
    Measurable (fun p : (E × (E →L[ℝ] E) × E) × E => scalarReply p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  unfold scalarReply
  fun_prop

theorem posteriorMeanUpdate_measurable :
    Measurable (fun p : (E × (E →L[ℝ] E) × E) × ℝ =>
      posteriorMeanUpdate p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  unfold posteriorMeanUpdate
  fun_prop

end NCBall
