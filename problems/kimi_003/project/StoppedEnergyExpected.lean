import StoppedEnergy

open MeasureTheory

namespace Task006.StoppedEnergy
noncomputable section
variable {W : Type*} [MeasurableSpace W] {μ : Measure W} [IsProbabilityMeasure μ]

/-- Finite telescoping from actual one-step expected energy increments. This
variant is useful after integrating genuine posterior swap inequalities. -/
theorem expected_energy_le_rankPotential_of_expected_increments
    (N d k : ℕ) (hkd : k ≤ d)
    (energy : ℕ → W → ℝ) (rank : ℕ → W → ℕ)
    (henergy : ∀ t ≤ N, Integrable (energy t) μ)
    (hpotential : ∀ t ≤ N, Integrable (fun w => rankPotential d (rank t w)) μ)
    (hzero : energy 0 =ᵐ[μ] (fun _ => 0))
    (hrankzero : rank 0 =ᵐ[μ] (fun _ => 0))
    (hrankcap : ∀ᵐ w ∂μ, rank N w ≤ k)
    (hstep : ∀ t < N,
      (∫ w, energy (t+1) w-energy t w ∂μ) ≤
      ∫ w, rankPotential d (rank (t+1) w)-rankPotential d (rank t w) ∂μ) :
    (∫ w, energy N w ∂μ) ≤ rankPotential d k := by
  have hind : ∀ t ≤ N, (∫ w, energy t w ∂μ) ≤ ∫ w, rankPotential d (rank t w) ∂μ := by
    intro t
    induction t with
    | zero =>
      intro ht
      have he : (∫ w, energy 0 w ∂μ) = 0 := by
        rw [integral_congr_ae hzero,integral_zero]
      have hp : (∫ w, rankPotential d (rank 0 w) ∂μ) = 0 := by
        have hh : (fun w => rankPotential d (rank 0 w)) =ᵐ[μ] (fun _ => 0) := by
          filter_upwards [hrankzero] with w hw
          simp [hw]
        rw [integral_congr_ae hh,integral_zero]
      rw [he,hp]
    | succ t ih =>
      intro ht
      have hs := hstep t (by omega)
      rw [integral_sub (henergy (t+1) ht) (henergy t (by omega)),
        integral_sub (hpotential (t+1) ht) (hpotential t (by omega))] at hs
      linarith [ih (by omega)]
  have h := hind N le_rfl
  have hpot : (∫ w, rankPotential d (rank N w) ∂μ) ≤ rankPotential d k := by
    have hh : (fun w => rankPotential d (rank N w)) ≤ᵐ[μ] (fun _ => rankPotential d k) := by
      filter_upwards [hrankcap] with w hw
      exact rankPotential_mono_below_dimension d (rank N w) k hw hkd
    have hp := integral_mono_ae (hpotential N le_rfl) (integrable_const (rankPotential d k)) hh
    simpa using hp
  exact h.trans hpot

#print axioms expected_energy_le_rankPotential_of_expected_increments
end
end Task006.StoppedEnergy
