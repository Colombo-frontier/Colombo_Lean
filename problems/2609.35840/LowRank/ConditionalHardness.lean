import LowRank.HardTransform
import LowRank.ProbabilityBounds

/-! The failure-probability reduction, with all unproved probabilistic and
Schatten inputs exposed in the theorem statement. This is not a proof of the
paper's minimax lower bound. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix

theorem success_bound_of_overlap_and_spectral_inputs
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : ℕ} {q k L c₀ C ε : ℝ}
    {W P K : Ω → Matrix (Fin d) (Fin d) ℝ} {S E : Set Ω}
    (hd : 0 < (d : ℝ)) (hk : 0 < k) (hL : 0 < L) (hc : 0 < c₀)
    (hq : q ≤ (d : ℝ) / 100) (hkd : k ≤ (d : ℝ) / 100)
    (hP : ∀ ω, IsOrthogonalProjector (P ω))
    (hK : ∀ ω, IsOrthogonalProjector (K ω))
    (htr : ∀ ω, (P ω).trace = k)
    (hW : ∀ ω ∈ E, (W ω).PosSemidef)
    (hupper : ∀ ω ∈ E, LoewnerLE (W ω) ((L / 2) • 1))
    (hgap : ∀ ω ∈ E,
      LoewnerLE ((c₀ * (k / d) ^ 2) • (1 - K ω)) (W ω))
    (hcompression : ∀ ω ∈ S ∩ E,
      k - (P ω * (hardMatrix L (W ω) * hardMatrix L (W ω))).trace ≤ C * ε * d)
    (hsmall : (((2 * L / 3) * C) / c₀) * ε * (d : ℝ) ^ 3 ≤ k ^ 3 / 4)
    (hbad : μ.real Eᶜ ≤ 1 / 20)
    (hzi : Integrable (fun ω => (P ω * K ω).trace) μ)
    (hposterior : (∫ ω, (P ω * K ω).trace ∂μ) ≤ 2 * k * (q + k) / (d - q)) :
    μ.real S ≤ 3 / 20 := by
  let T : Set Ω := {ω | 3 * k / 4 ≤ (P ω * K ω).trace}
  have hST : S ∩ E ⊆ T := by
    intro ω hω
    have henergy := compression_deficit_to_energy hL (hW ω hω.2)
      (hP ω) (htr ω) (hupper ω hω.2) (hcompression ω hω)
    have henergy' : (P ω * W ω).trace ≤ ((2 * L / 3) * C) * ε * d := by
      nlinarith only [henergy]
    have hdef := wishart_gap_overlap_deficit (hP ω) hc hk hd (htr ω)
      (hgap ω hω.2) henergy'
    exact overlap_of_cubic_smallness hk hdef hsmall
  have hz : 0 ≤ᵐ[μ] (fun ω => (P ω * K ω).trace) :=
    Filter.Eventually.of_forall (fun ω => projector_overlap_nonneg (hP ω) (hK ω))
  have hT : μ.real T ≤ 1 / 10 :=
    (overlap_tail_bound hk hzi hz hposterior).trans (overlap_tail_constant hd hq hkd)
  exact success_probability_of_good_event hST hbad hT

end LowRank
