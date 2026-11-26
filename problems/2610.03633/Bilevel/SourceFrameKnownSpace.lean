import Bilevel.SourceFrameObservation
import Bilevel.SourceFrameEnergyEvent
import Bilevel.TransportObserverBlock

/-! Named revelations belong to the actual accumulated subspace. Energy
bounds transfer to any smaller source-known space, without identifying
the stronger selected-frame observation spaces across different frames. -/
noncomputable section
universe u
namespace Bilevel.SourceFrameActions
open EuclideanGaussian ProjectionPosterior ProjectionGeometry TransportControllerMachine

variable {H : Memory.{u}} {d T : ℕ}

def KnownInSpace (s : State H d T) (U : Frame d T) : Prop := ∀ k∈s.2.2, U k∈s.2.1

theorem known_observeStep (L : Rules H d T) (t : ℕ) (s : State H d T) (U : Frame d T)
    (hs : KnownInSpace s U) : KnownInSpace (observeStep L t s U) U := by
  intro k hk
  by_cases hr : L.request t s.1=true
  · simp only [observeStep,if_pos hr] at hk ⊢
    rcases Set.mem_insert_iff.mp hk with he | ho
    · subst k
      exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (hs k ho)))
  · simp only [observeStep,if_neg hr] at hk ⊢
    exact Submodule.mem_sup_left (Submodule.mem_sup_left (hs k hk))

theorem known_observeRun (L : Rules H d T) : ∀ n t (s : State H d T) (U : Frame d T),
    KnownInSpace s U → KnownInSpace (observeRun L n t s U) U := by
  intro n
  induction n with
  | zero => intros; assumption
  | succ n ih => exact fun t s U hs => ih (t+1) _ U (known_observeStep L t s U hs)

theorem known_initial (h : H) (U : Frame d T) : KnownInSpace (h,(⊥,∅)) U := by
  intro k hk
  exact False.elim hk

theorem boundedEnergy_subspace {W V : Submodule ℝ (Space d)} (hWV : W≤V)
    (K : Set (Fin T)) (U : Frame d T) (cap : ℝ)
    (hE : GenieProtocol.BoundedEnergy V K U cap) : GenieProtocol.BoundedEnergy W K U cap := by
  intro k hk
  have hnorm := TransportObserver.project_norm_mono hWV (U k)
  exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnorm).trans (hE k hk)

end Bilevel.SourceFrameActions
