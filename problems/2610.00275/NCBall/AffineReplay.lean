import NCBall.OracleTranscript
import NCBall.ChargedSmallBall

/-! # Replaying affine scalar replies using the proved linear Gaussian experiment -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace ENNReal
namespace NCBall

variable {S F : Type*} [MeasurableSpace S]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] {H : ℕ}

def affineHistoryReplay (offset : (t : ℕ) → LinearHistory S t → ℝ) :
    (t : ℕ) → LinearHistory S t → LinearHistory S t
  | 0, h => h
  | t + 1, h =>
      let g := affineHistoryReplay offset t h.1
      (g, offset t g + h.2)

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F]
  [BorelSpace F] [FiniteDimensional ℝ F] in
theorem affineHistoryReplay_measurable (offset : (t : ℕ) → LinearHistory S t → ℝ)
    (ho : ∀ t, Measurable (offset t)) (t : ℕ) : Measurable (affineHistoryReplay offset t) := by
  induction t with
  | zero => exact measurable_id
  | succ t ih =>
    exact (ih.comp measurable_fst).prodMk (((ho t).comp (ih.comp measurable_fst)).add measurable_snd)

def replayedReusablePolicy (p : ReusableQueryPolicy S F H)
    (offset : (t : ℕ) → LinearHistory S t → ℝ) (ho : ∀ t, Measurable (offset t)) :
    ReusableQueryPolicy S F H where
  handle t h := p.handle t (affineHistoryReplay offset t h)
  direction t h := p.direction t (affineHistoryReplay offset t h)
  measurable_handle t := (p.measurable_handle t).comp (affineHistoryReplay_measurable offset ho t)
  measurable_direction t := (p.measurable_direction t).comp (affineHistoryReplay_measurable offset ho t)

def affineReusableReply (p : ReusableQueryPolicy S F H) (σ : ℝ)
    (offset : (t : ℕ) → LinearHistory S t → ℝ)
    (t : ℕ) (h : LinearHistory S t) (z : HandleLatent F H) : ℝ :=
  offset t h + ⟪noisyHandleDirection F σ (p.handle t h) (p.direction t h), z⟫_ℝ

attribute [local irreducible] noisyHandleDirection

omit [FiniteDimensional ℝ F] in
theorem affineTranscript_replay (p : ReusableQueryPolicy S F H) (σ : ℝ)
    (offset : (t : ℕ) → LinearHistory S t → ℝ) (ho : ∀ t, Measurable (offset t))
    (t : ℕ) (w : S × HandleLatent F H) :
    oracleTranscript (affineReusableReply p σ offset) t w =
      affineHistoryReplay offset t
        (linearTranscript ((replayedReusablePolicy p offset ho).toLinear σ) t w) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [oracleTranscript, affineHistoryReplay, linearTranscript, ih,
      affineReusableReply, ReusableQueryPolicy.toLinear, replayedReusablePolicy]

omit [InnerProductSpace ℝ F] [BorelSpace F] [FiniteDimensional ℝ F] in
theorem affineReplay_queryCount (p : ReusableQueryPolicy S F H)
    (offset : (t : ℕ) → LinearHistory S t → ℝ) (ho : ∀ t, Measurable (offset t))
    (t : ℕ) (h : LinearHistory S t) :
    reusableQueryCount p t (affineHistoryReplay offset t h) =
      reusableQueryCount (replayedReusablePolicy p offset ho) t h := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [reusableQueryCount, affineHistoryReplay, ih, replayedReusablePolicy]

theorem affine_reusable_estimation_bound (ν : Measure S) [IsProbabilityMeasure ν]
    (p : ReusableQueryPolicy S F H) (σ : ℝ) (hσ : 0 < σ)
    (offset : (t : ℕ) → LinearHistory S t → ℝ) (ho : ∀ t, Measurable (offset t)) (t : ℕ)
    (hn : 0 < Module.finrank ℝ F) (u : LinearHistory S t → F) (hu : Measurable u) :
    (ν.prod (euclideanGaussianLaw (HandleLatent F H)))
      {w | (reusableQueryCount p t (oracleTranscript (affineReusableReply p σ offset) t w) : ℝ) <
        (Module.finrank ℝ F : ℝ) * σ ^ 2 / 16 ∧
        ‖(Real.sqrt (Module.finrank ℝ F : ℝ))⁻¹ • hiddenBlock F H w.2 -
          u (oracleTranscript (affineReusableReply p σ offset) t w)‖ ≤ 1 / 16} ≤
      ENNReal.ofReal (Real.exp (-(Module.finrank ℝ F : ℝ) / 8)) := by
  simp_rw [affineTranscript_replay p σ offset ho, affineReplay_queryCount p offset ho]
  exact charged_adaptive_estimation_bound ν (replayedReusablePolicy p offset ho) σ hσ t hn
    (u ∘ affineHistoryReplay offset t) (hu.comp (affineHistoryReplay_measurable offset ho t))

end NCBall
