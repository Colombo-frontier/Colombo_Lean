import NCBall.GaussianQueryStep

/-! # Actual histories and posterior statistics of adaptive scalar queries -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
namespace NCBall

def LinearHistory (S : Type*) : ℕ → Type _
  | 0 => S
  | t + 1 => LinearHistory S t × ℝ

instance linearHistoryMeasurableSpace (S : Type*) [MeasurableSpace S] :
    (t : ℕ) → MeasurableSpace (LinearHistory S t)
  | 0 => inferInstanceAs (MeasurableSpace S)
  | t + 1 => by
    letI : MeasurableSpace (LinearHistory S t) := linearHistoryMeasurableSpace S t
    exact inferInstanceAs (MeasurableSpace (LinearHistory S t × ℝ))

variable (S E : Type*) [MeasurableSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

structure LinearQueryPolicy where
  query : (t : ℕ) → LinearHistory S t → E
  measurable_query : ∀ t, Measurable (query t)

variable {S E}

def linearTranscript (p : LinearQueryPolicy S E) :
    (t : ℕ) → S × E → LinearHistory S t
  | 0, w => w.1
  | t + 1, w =>
    let h := linearTranscript p t w
    (h, ⟪p.query t h, w.2⟫_ℝ)

def linearPosteriorProjection (p : LinearQueryPolicy S E) :
    (t : ℕ) → LinearHistory S t → E →L[ℝ] E
  | 0, _ => ContinuousLinearMap.id ℝ E
  | t + 1, h => residualUpdate (linearPosteriorProjection p t h.1) (p.query t h.1)

def linearPosteriorMean (p : LinearQueryPolicy S E) :
    (t : ℕ) → LinearHistory S t → E
  | 0, _ => 0
  | t + 1, h => posteriorMeanUpdate (linearPosteriorMean p t h.1)
      (linearPosteriorProjection p t h.1) (p.query t h.1) h.2

theorem linearTranscript_measurable (p : LinearQueryPolicy S E) (t : ℕ) :
    Measurable (linearTranscript p t) := by
  induction t with
  | zero => exact measurable_fst
  | succ t ih =>
    exact ih.prodMk (((p.measurable_query t).comp ih).inner measurable_snd)

theorem linearPosteriorProjection_measurable (p : LinearQueryPolicy S E) (t : ℕ) :
    Measurable (linearPosteriorProjection p t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    exact (residualUpdate_measurable (E := E)).comp
      ((ih.comp measurable_fst).prodMk ((p.measurable_query t).comp measurable_fst))

theorem linearPosteriorMean_measurable (p : LinearQueryPolicy S E) (t : ℕ) :
    Measurable (linearPosteriorMean p t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hQ := linearPosteriorProjection_measurable p t
    exact (posteriorMeanUpdate_measurable (E := E)).comp
      (((ih.comp measurable_fst).prodMk
        ((hQ.comp measurable_fst).prodMk ((p.measurable_query t).comp measurable_fst))).prodMk
          measurable_snd)

omit [BorelSpace E] [FiniteDimensional ℝ E] in
theorem linearPosteriorProjection_isProjection (p : LinearQueryPolicy S E) (t : ℕ)
    (h : LinearHistory S t) : IsResidualProjection (linearPosteriorProjection p t h) := by
  induction t with
  | zero => exact isResidualProjection_id
  | succ t ih => exact residualUpdate_isProjection (ih h.1) (p.query t h.1)

omit [BorelSpace E] [FiniteDimensional ℝ E] in
/-- The mean and residual projection are computed solely from recorded replies. -/
theorem linearTranscript_reconstruction (p : LinearQueryPolicy S E) (t : ℕ) (w : S × E) :
    linearPosteriorMean p t (linearTranscript p t w) +
      linearPosteriorProjection p t (linearTranscript p t w) w.2 = w.2 := by
  induction t with
  | zero => simp [linearTranscript, linearPosteriorMean, linearPosteriorProjection]
  | succ t ih =>
    let h := linearTranscript p t w
    let m := linearPosteriorMean p t h
    let Q := linearPosteriorProjection p t h
    let a := p.query t h
    have hQ := linearPosteriorProjection_isProjection p t h
    have hr : ⟪a, w.2⟫_ℝ = scalarReply m Q a w.2 := by
      unfold scalarReply
      change ⟪a, w.2⟫_ℝ = ⟪a, linearPosteriorMean p t h + linearPosteriorProjection p t h w.2⟫_ℝ
      rw [ih]
    change posteriorMeanUpdate m Q a ⟪a, w.2⟫_ℝ + residualUpdate Q a w.2 = w.2
    rw [hr, posteriorMeanUpdate_reply m hQ]
    change (m + rankProjection (Q a) w.2) + (Q w.2 - rankProjection (Q a) w.2) = w.2
    convert ih using 1
    dsimp [m, Q, h]
    abel

end NCBall
