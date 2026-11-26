import Bilevel.SourceFrameBatchObservation

/-! The source memory and named columns are independent of the auxiliary
observation space. Batching preserves this pair exactly at call boundaries. -/
noncomputable section
open MeasureTheory
universe u
namespace Bilevel.SourceFrameActions
open EuclideanGaussian ProjectionPosterior TransportControllerMachine

variable {H : Memory.{u}} {d T B : ℕ}

def shadow (s : State H d T) := (s.1,s.2.2)

theorem observeStep_shadow_congr (L : Rules H d T) (t : ℕ) (s z : State H d T)
    (U : Frame d T) (hs : shadow s=shadow z) :
    shadow (observeStep L t s U)=shadow (observeStep L t z U) := by
  rcases s with ⟨a,V,K⟩
  rcases z with ⟨b,W,N⟩
  change (a,K)=(b,N) at hs
  obtain ⟨ha,hk⟩ := Prod.mk.inj hs
  cases ha
  cases hk
  by_cases hr : L.request t a=true
  · simp only [observeStep,if_pos hr,shadow]
  · simp only [observeStep,if_neg hr,shadow]


end Bilevel.SourceFrameActions

