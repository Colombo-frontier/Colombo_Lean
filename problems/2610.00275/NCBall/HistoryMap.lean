import NCBall.HistorySeed
import NCBall.ShadowState

/-! # Adding independent background data to the seed preserves the original algorithm -/

noncomputable section
open MeasureTheory
namespace NCBall

variable {S R Ω Ω' : Type*}

def mapHistorySeed (f : S → R) : (t : ℕ) → LinearHistory S t → LinearHistory R t
  | 0, h => f h
  | t + 1, h => (mapHistorySeed f t h.1, h.2)

theorem mapHistorySeed_seed (f : S → R) (t : ℕ) (h : LinearHistory S t) :
    historySeed t (mapHistorySeed f t h) = f (historySeed t h) := by
  induction t with
  | zero => rfl
  | succ t ih => exact ih h.1

theorem mapHistorySeed_measurable [MeasurableSpace S] [MeasurableSpace R]
    (f : S → R) (hf : Measurable f) (t : ℕ) : Measurable (mapHistorySeed f t) := by
  induction t with
  | zero => exact hf
  | succ t ih => exact (ih.comp measurable_fst).prodMk measurable_snd

theorem oracleTranscript_map_seed (f : S → R) (g : S → Ω → Ω')
    (reply : (t : ℕ) → LinearHistory S t → Ω → ℝ)
    (reply' : (t : ℕ) → LinearHistory R t → Ω' → ℝ)
    (hreply : ∀ t h z, reply t h z = reply' t (mapHistorySeed f t h) (g (historySeed t h) z))
    (t : ℕ) (w : S × Ω) :
    mapHistorySeed f t (oracleTranscript reply t w) =
      oracleTranscript reply' t (f w.1, g w.1 w.2) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [oracleTranscript, mapHistorySeed, hreply, oracleTranscript_seed, ih]

variable [MeasurableSpace S] [MeasurableSpace R] {n H : ℕ}

def liftRoomPolicy (p : RoomQueryPolicy R n H) (f : S → R) (hf : Measurable f) :
    RoomQueryPolicy S n H where
  point t h := p.point t (mapHistorySeed f t h)
  handle t h := p.handle t (mapHistorySeed f t h)
  measurable_point t := (p.measurable_point t).comp (mapHistorySeed_measurable f hf t)
  measurable_handle t := (p.measurable_handle t).comp (mapHistorySeed_measurable f hf t)

theorem shadowCounter_lift (p : RoomQueryPolicy R n H) (f : S → R) (hf : Measurable f)
    (ρ : ℝ) (q₀ t : ℕ) (h : LinearHistory S t) :
    shadowCounter (liftRoomPolicy p f hf) ρ q₀ t h =
      shadowCounter p ρ q₀ t (mapHistorySeed f t h) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [shadowCounter, mapHistorySeed, ih]
    rfl

theorem shadowStage_lift (p : RoomQueryPolicy R n H) (f : S → R) (hf : Measurable f)
    (ρ : ℝ) (q₀ t : ℕ) (h : LinearHistory S t) :
    shadowStage (liftRoomPolicy p f hf) ρ q₀ t h =
      shadowStage p ρ q₀ t (mapHistorySeed f t h) := by
  simp only [shadowStage, shadowCounter_lift]

end NCBall
