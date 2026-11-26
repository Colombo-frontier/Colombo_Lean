import NCBall.ChainProbabilityScale
import NCBall.FunctionClass

/-! # Actual gradient success on good hidden instances

The success event is evaluated on the real scalar oracle transcript, with the
same latent table supplying its reusable noise. The good event constrains only
the hidden directions. No unconditional stationary-point claim is used.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NCBall

variable {R : Type*} [MeasurableSpace R] {n H M : ℕ}

def latentGoodEvent (scale : ℝ) : Set (RoomLatents n H M) :=
  {w | ∀ j < M, ‖latentDirections scale w j‖ ≤ 2}

def fullPopulation (ρ γ lam scale : ℝ) (w : RoomLatents n H M) : Space n → ℝ :=
  chainValue M ρ γ lam (fullRoomCenters ρ scale w) (latentDirections scale w)

def fullGradientSuccess (p : RoomQueryPolicy R n H) (ρ η σ scale : ℝ)
    (N : ℕ) (out : LinearHistory R N → Space n) : Set (R × RoomLatents n H M) :=
  {w | ‖gradient (fullPopulation ρ (4 * η) (calibratedLam (4 * η)) scale w.2)
    (out (oracleTranscript (fullRealReply p ρ (4 * η) (calibratedLam (4 * η)) σ scale) N w))‖ ≤ η}

theorem full_success_on_good_subset_terminal (p : RoomQueryPolicy R n H)
    {ρ η : ℝ} (hρ : 0 < ρ) (hη : 0 < η) (σ scale : ℝ)
    (N : ℕ) (out : LinearHistory R N → Space n) :
    fullGradientSuccess (M := M) p ρ η σ scale N out ∩ (Prod.snd ⁻¹' latentGoodEvent scale) ⊆
      fullRealTerminalEvent p ρ (4 * η) (calibratedLam (4 * η)) σ scale N out := by
  rintro w ⟨hs, hg⟩
  exact stationary_point_in_terminal_room hρ hη (latentDirections scale w.2)
    (latentDirections_clock scale w.2) hg _ hs

theorem full_success_on_good_quarter (ν : Measure R) [IsProbabilityMeasure ν]
    (p : RoomQueryPolicy R n H) {q₀ N : ℕ} (hq : 0 < q₀) (hN : N < M * q₀) (hn : 0 < n)
    {ρ σ η : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (hη : 0 < η)
    (hqcap : (q₀ : ℝ) ≤ n * σ ^ 2 / 16)
    (hlog : 40 * Real.log (2 + (M * q₀ : ℕ)) ≤ n)
    (out : LinearHistory R N → Space n) (hout : Measurable out) :
    (ν.prod (roomLatentLaw n H M))
      (fullGradientSuccess p ρ η σ (Real.sqrt (n : ℝ))⁻¹ N out ∩
        (Prod.snd ⁻¹' latentGoodEvent (Real.sqrt (n : ℝ))⁻¹)) ≤ 1 / 4 :=
  (measure_mono (full_success_on_good_subset_terminal p hρ hη σ _ N out)).trans
    (full_chain_terminal_quarter ν p hq hN hn hρ hσ (4 * η) (calibratedLam (4 * η))
      hqcap hlog out hout)

end NCBall
