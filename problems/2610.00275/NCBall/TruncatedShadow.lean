import NCBall.ShadowMeasurable
import NCBall.ShadowSplice
import NCBall.HistorySeed
import NCBall.AffineReplay
import NCBall.GaussianHandleLaw

/-! # One-room truncation as a measurable affine reusable Gaussian experiment -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace NCBall

variable (S : Type*) [MeasurableSpace S] (n H : ℕ)

structure RoomBackground where
  directions : S → ℕ → Space n
  samples : S → Fin H → ℕ → Space n
  measurable_directions : ∀ k, Measurable (fun s => directions s k)
  measurable_samples : ∀ k, Measurable (fun sh : S × Fin H => samples sh.1 sh.2 k)

variable {S n H}

def backgroundCenters (d : RoomBackground S n H) (ρ : ℝ)
    (t : ℕ) (h : LinearHistory S t) : ℕ → Space n :=
  roomCenter ρ (d.directions (historySeed t h))

def backgroundSamples (d : RoomBackground S n H) (p : RoomQueryPolicy S n H)
    (t : ℕ) (h : LinearHistory S t) : ℕ → Space n :=
  d.samples (historySeed t h) (p.handle t h)

theorem backgroundCenters_measurable (d : RoomBackground S n H) (ρ : ℝ) (t j : ℕ) :
    Measurable (fun h : LinearHistory S t => backgroundCenters d ρ t h j) :=
  (roomCenter_measurable_data ρ d.directions d.measurable_directions j).comp (historySeed_measurable t)

theorem backgroundSamples_measurable (d : RoomBackground S n H) (p : RoomQueryPolicy S n H)
    (t j : ℕ) : Measurable (fun h : LinearHistory S t => backgroundSamples d p t h j) :=
  (d.measurable_samples j).comp ((historySeed_measurable t).prodMk (p.measurable_handle t))

def truncatedShadowOffset (d : RoomBackground S n H) (p : RoomQueryPolicy S n H)
    (M q₀ j : ℕ) (ρ γ lam : ℝ) (t : ℕ) (h : LinearHistory S t) : ℝ :=
  let r := shadowStage p ρ q₀ t h
  if r < j then shadowValue M r ρ γ lam (backgroundCenters d ρ t h)
      (backgroundSamples d p t h) (p.point t h)
  else if r = j then shadowPastValue j ρ γ lam (backgroundCenters d ρ t h)
      (backgroundSamples d p t h) (p.point t h)
  else 0

def truncatedShadowDirection (d : RoomBackground S n H) (p : RoomQueryPolicy S n H)
    (q₀ j : ℕ) (ρ lam scale : ℝ) (t : ℕ) (h : LinearHistory S t) : Transverse n :=
  if shadowStage p ρ q₀ t h = j then scale • transverseProjection n
    (roomMeasurement ρ lam (backgroundCenters d ρ t h j) (p.point t h)) else 0

theorem truncatedShadowOffset_measurable (d : RoomBackground S n H) (p : RoomQueryPolicy S n H)
    (M q₀ j : ℕ) (ρ γ lam : ℝ) (t : ℕ) :
    Measurable (truncatedShadowOffset d p M q₀ j ρ γ lam t) := by
  have hr := shadowStage_measurable p ρ q₀ t
  have hc := backgroundCenters_measurable d ρ t
  have hv := backgroundSamples_measurable d p t
  have hp := p.measurable_point t
  exact Measurable.ite (measurableSet_lt hr measurable_const)
    (shadowValue_measurable_data M ρ γ lam _ _ _ _ hr hc hv hp)
    (Measurable.ite (hr (measurableSet_singleton j))
      (shadowPastValue_measurable_data j ρ γ lam _ _ _ hc hv hp) measurable_const)

theorem truncatedShadowDirection_measurable (d : RoomBackground S n H) (p : RoomQueryPolicy S n H)
    (q₀ j : ℕ) (ρ lam scale : ℝ) (t : ℕ) :
    Measurable (truncatedShadowDirection d p q₀ j ρ lam scale t) := by
  have hr := shadowStage_measurable p ρ q₀ t
  have hc := backgroundCenters_measurable d ρ t j
  have hp := p.measurable_point t
  have hm := (roomMeasurement_continuous (n := n) ρ lam).measurable.comp (hc.prodMk hp)
  exact Measurable.ite (hr (measurableSet_singleton j))
    (((transverseProjection n).measurable.comp hm).const_smul scale) measurable_const

def truncatedShadowPolicy (d : RoomBackground S n H) (p : RoomQueryPolicy S n H)
    (q₀ j : ℕ) (ρ lam scale : ℝ) : ReusableQueryPolicy S (Transverse n) H where
  handle := p.handle
  direction := truncatedShadowDirection d p q₀ j ρ lam scale
  measurable_handle := p.measurable_handle
  measurable_direction := truncatedShadowDirection_measurable d p q₀ j ρ lam scale

end NCBall
