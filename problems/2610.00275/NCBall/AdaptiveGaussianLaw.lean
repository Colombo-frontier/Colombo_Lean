import NCBall.LinearTranscript

/-! # The actual joint law after finitely many adaptive linear observations -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
namespace NCBall

variable {S E : Type*} [MeasurableSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def linearHistoryLaw (ν : Measure S) (p : LinearQueryPolicy S E) (t : ℕ) :
    Measure (LinearHistory S t) :=
  (ν.prod (euclideanGaussianLaw E)).map (linearTranscript p t)

instance linearHistoryLaw_probability (ν : Measure S) [IsProbabilityMeasure ν]
    (p : LinearQueryPolicy S E) (t : ℕ) : IsProbabilityMeasure (linearHistoryLaw ν p t) :=
  isProbabilityMeasure_map (linearTranscript_measurable p t).aemeasurable

def linearPosteriorRepresentation (p : LinearQueryPolicy S E) (t : ℕ)
    (hz : LinearHistory S t × E) : LinearHistory S t × E :=
  (hz.1, linearPosteriorMean p t hz.1 + linearPosteriorProjection p t hz.1 hz.2)

theorem linearPosteriorRepresentation_measurable (p : LinearQueryPolicy S E) (t : ℕ) :
    Measurable (linearPosteriorRepresentation p t) := by
  have hm := linearPosteriorMean_measurable p t
  have hQ := linearPosteriorProjection_measurable p t
  unfold linearPosteriorRepresentation
  fun_prop

/-- A seed of arbitrary probability law is permitted. The transcript is generated
by querying the original, fixed latent vector; the conditional Gaussian form
is a conclusion of the induction, not an assumption about the transcript. -/
theorem adaptive_gaussian_joint_law (ν : Measure S) [IsProbabilityMeasure ν]
    (p : LinearQueryPolicy S E) (t : ℕ) :
    (ν.prod (euclideanGaussianLaw E)).map
      (fun w : S × E => (linearTranscript p t w, w.2)) =
      ((linearHistoryLaw ν p t).prod (euclideanGaussianLaw E)).map
        (linearPosteriorRepresentation p t) := by
  induction t with
  | zero =>
    have hrep : linearPosteriorRepresentation p 0 = (id : S × E → S × E) := by
      funext hz
      simp [linearPosteriorRepresentation, linearPosteriorMean, linearPosteriorProjection]
    rw [hrep, Measure.map_id]
    change (ν.prod (euclideanGaussianLaw E)).map (fun w : S × E => (w.1, w.2)) =
      ((ν.prod (euclideanGaussianLaw E)).map Prod.fst).prod (euclideanGaussianLaw E)
    simp only [Prod.mk.eta, Measure.map_id', Measure.map_fst_prod, measure_univ, one_smul]
  | succ t ih =>
    let μ := ν.prod (euclideanGaussianLaw E)
    let τ := linearHistoryLaw ν p t
    let joint : S × E → LinearHistory S t × E := fun w => (linearTranscript p t w, w.2)
    let obs : LinearHistory S t × E → LinearHistory S (t + 1) := fun hz =>
      (hz.1, ⟪p.query t hz.1, hz.2⟫_ℝ)
    let adv : LinearHistory S t × E → LinearHistory S (t + 1) × E := fun hz => (obs hz, hz.2)
    let reply : LinearHistory S t × E → LinearHistory S (t + 1) := fun hz =>
      (hz.1, scalarReply (linearPosteriorMean p t hz.1) (linearPosteriorProjection p t hz.1)
        (p.query t hz.1) hz.2)
    have hjoint : Measurable joint := (linearTranscript_measurable p t).prodMk measurable_snd
    have hquery := p.measurable_query t
    have hmean := linearPosteriorMean_measurable p t
    have hproj := linearPosteriorProjection_measurable p t
    have hobs : Measurable obs := by
      change Measurable (fun hz : LinearHistory S t × E => (hz.1, ⟪p.query t hz.1, hz.2⟫_ℝ))
      fun_prop
    have hadv : Measurable adv := hobs.prodMk measurable_snd
    have hrep := linearPosteriorRepresentation_measurable p t
    have hnext : linearHistoryLaw ν p (t + 1) =
        (τ.prod (euclideanGaussianLaw E)).map reply := by
      calc
        _ = (μ.map joint).map obs := by
          rw [Measure.map_map hobs hjoint]
          rfl
        _ = (((τ.prod (euclideanGaussianLaw E)).map (linearPosteriorRepresentation p t))).map obs := by
          rw [ih]
        _ = _ := by
          rw [Measure.map_map hobs hrep]
          rfl
    calc
      _ = (μ.map joint).map adv := by
        rw [Measure.map_map hadv hjoint]
        rfl
      _ = (((τ.prod (euclideanGaussianLaw E)).map (linearPosteriorRepresentation p t))).map adv := by
        rw [ih]
      _ = (τ.prod (euclideanGaussianLaw E)).map
          (fun hz : LinearHistory S t × E => ((hz.1,
            scalarReply (linearPosteriorMean p t hz.1) (linearPosteriorProjection p t hz.1)
              (p.query t hz.1) hz.2),
            linearPosteriorMean p t hz.1 + linearPosteriorProjection p t hz.1 hz.2)) := by
        rw [Measure.map_map hadv hrep]
        rfl
      _ = _ := by
        rw [gaussian_scalar_query_joint_law τ (linearPosteriorMean p t)
          (linearPosteriorProjection p t) (p.query t) hmean hproj hquery
          (linearPosteriorProjection_isProjection p t)]
        change (((τ.prod (euclideanGaussianLaw E)).map reply).prod (euclideanGaussianLaw E)).map
          (linearPosteriorRepresentation p (t + 1)) = _
        rw [← hnext]

end NCBall
