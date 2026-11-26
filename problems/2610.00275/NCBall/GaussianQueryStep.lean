import NCBall.GaussianRefresh

/-! # The joint-law identity for one adaptive Gaussian linear query -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
namespace NCBall

theorem map_prod_left {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure C) [SFinite μ] [SFinite ν] (f : A → B) (hf : Measurable f) :
    (μ.map f).prod ν = (μ.prod ν).map (Prod.map f id) := by
  simpa only [Measure.map_id] using Measure.map_prod_map μ ν hf measurable_id

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem adaptive_projectionRefresh_assoc {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [SFinite ν] (b : S → E) (hb : Measurable b) :
    ((ν.prod (euclideanGaussianLaw E)).prod (euclideanGaussianLaw E)).map
      (fun p : (S × E) × E => (p.1.1, projectionRefresh (b p.1.1) (p.1.2, p.2))) =
      ν.prod (euclideanGaussianLaw E) := by
  have h := adaptive_projectionRefresh_law ν b hb
  have hm : Measurable (fun p : S × (E × E) => (p.1, projectionRefresh (b p.1) p.2)) := by
    simp only [projectionRefresh, rankProjection_apply]
    fun_prop
  rw [← Measure.prodAssoc_prod, Measure.map_map hm MeasurableEquiv.prodAssoc.measurable] at h
  exact h

/-- Joint law of the actual reply and latent vector, expressed through the
updated affine Gaussian slice. This includes zero/redundant query directions. -/
theorem gaussian_scalar_query_joint_law {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [SFinite ν]
    (m : S → E) (Q : S → E →L[ℝ] E) (a : S → E)
    (hm : Measurable m) (hQm : Measurable Q) (ha : Measurable a)
    (hQ : ∀ s, IsResidualProjection (Q s)) :
    (ν.prod (euclideanGaussianLaw E)).map
      (fun p : S × E => ((p.1, scalarReply (m p.1) (Q p.1) (a p.1) p.2), m p.1 + Q p.1 p.2)) =
    (((ν.prod (euclideanGaussianLaw E)).map
      (fun p : S × E => (p.1, scalarReply (m p.1) (Q p.1) (a p.1) p.2))).prod
        (euclideanGaussianLaw E)).map
      (fun p : (S × ℝ) × E => (p.1,
        posteriorMeanUpdate (m p.1.1) (Q p.1.1) (a p.1.1) p.1.2 +
          residualUpdate (Q p.1.1) (a p.1.1) p.2)) := by
  let reply : S × E → S × ℝ := fun p =>
    (p.1, scalarReply (m p.1) (Q p.1) (a p.1) p.2)
  let before : S × E → (S × ℝ) × E := fun p => (reply p, m p.1 + Q p.1 p.2)
  let after : (S × ℝ) × E → (S × ℝ) × E := fun p => (p.1,
    posteriorMeanUpdate (m p.1.1) (Q p.1.1) (a p.1.1) p.1.2 +
      residualUpdate (Q p.1.1) (a p.1.1) p.2)
  let combine : (S × E) × E → S × E := fun p =>
    (p.1.1, projectionRefresh (Q p.1.1 (a p.1.1)) (p.1.2, p.2))
  have hreply : Measurable reply := by
    unfold reply scalarReply
    fun_prop
  have hbefore : Measurable before := by
    unfold before
    exact hreply.prodMk (by fun_prop)
  have hafter : Measurable after := by
    have hinput : Measurable (fun p : (S × ℝ) × E =>
        ((m p.1.1, Q p.1.1, a p.1.1), p.1.2)) := by fun_prop
    have hmean : Measurable (fun p : (S × ℝ) × E =>
        posteriorMeanUpdate (m p.1.1) (Q p.1.1) (a p.1.1) p.1.2) :=
      (posteriorMeanUpdate_measurable (E := E)).comp hinput
    have hresinput : Measurable (fun p : (S × ℝ) × E => (Q p.1.1, a p.1.1)) := by fun_prop
    have hres : Measurable (fun p : (S × ℝ) × E => residualUpdate (Q p.1.1) (a p.1.1)) :=
      (residualUpdate_measurable (E := E)).comp hresinput
    unfold after
    exact measurable_fst.prodMk (hmean.add (by fun_prop))
  have hcombine : Measurable combine := by
    unfold combine
    simp only [projectionRefresh, rankProjection_apply]
    fun_prop
  have hcombineLaw := adaptive_projectionRefresh_assoc ν (fun s => Q s (a s)) (by fun_prop)
  change ((ν.prod (euclideanGaussianLaw E)).map before) =
    (((ν.prod (euclideanGaussianLaw E)).map reply).prod (euclideanGaussianLaw E)).map after
  calc
    _ = (((ν.prod (euclideanGaussianLaw E)).prod (euclideanGaussianLaw E))).map
        (before ∘ combine) := by
      rw [← Measure.map_map hbefore hcombine, hcombineLaw]
    _ = (((ν.prod (euclideanGaussianLaw E)).prod (euclideanGaussianLaw E))).map
        (after ∘ Prod.map reply id) := by
      congr 1
      funext p
      dsimp [before, combine, after, reply]
      rw [scalarReply_refresh (m p.1.1) (hQ p.1.1),
        posterior_refresh_identity (m p.1.1) (hQ p.1.1)]
    _ = _ := by
      rw [← Measure.map_map hafter (hreply.prodMap measurable_id),
        ← map_prod_left _ _ reply hreply]

end NCBall
