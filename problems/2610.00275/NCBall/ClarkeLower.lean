import NCBall.ClarkeSmooth
import NCBall.GoldsteinLower

/-! # The lower-bound success event uses the Clarke Goldstein residual -/

noncomputable section
open MeasureTheory Set
namespace NCBall

def fullClarkeSuccess {Seed : Type*} [MeasurableSpace Seed] {n K M : ℕ}
    (p : RoomQueryPolicy Seed n K) (ρ η σ scale δ ε : ℝ)
    (N : ℕ) (out : LinearHistory Seed N → Space n) : Set (Seed × RoomLatents n K M) :=
  {w | clarkeGoldsteinResidual
    (fullPopulation ρ (4 * η) (calibratedLam (4 * η)) scale w.2) δ
    (out (oracleTranscript (fullRealReply p ρ (4 * η) (calibratedLam (4 * η)) σ scale) N w)) ≤ ε}

theorem fullClarkeSuccess_eq {Seed : Type*} [MeasurableSpace Seed] {n K M : ℕ}
    (p : RoomQueryPolicy Seed n K) (ρ η σ scale δ ε : ℝ)
    (N : ℕ) (out : LinearHistory Seed N → Space n) :
    fullClarkeSuccess (M := M) p ρ η σ scale δ ε N out =
      fullGoldsteinSuccess p ρ η σ scale δ ε N out := by
  ext w
  have hf : ContDiff ℝ 1 (fullPopulation (M := M) ρ (4 * η) (calibratedLam (4 * η)) scale w.2) :=
    (chainValue_smooth _ _ _ _ _ _).of_le (by norm_num)
  change clarkeGoldsteinResidual _ δ _ ≤ ε ↔ smoothGoldsteinResidual _ δ _ ≤ ε
  rw [clarkeGoldsteinResidual_eq_of_C1 hf]

end NCBall
