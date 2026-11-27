import Mathlib

/-!
Finite-horizon stopped-rank energy accounting. The terminal expectation is
proved from local conditional drift inequalities, rather than assumed.
Connecting those local inequalities to arbitrary adaptive spherical
measurements remains a separate geometric/probabilistic obligation.
-/

open MeasureTheory ProbabilityTheory Set

namespace Task006.StoppedEnergy

noncomputable section

/-- The rank-compensating harmonic potential. -/
def rankPotential (d r : ℕ) : ℝ :=
  ∑ j ∈ Finset.range r, (1 : ℝ) / ((d : ℝ) - j)

@[simp] theorem rankPotential_zero (d : ℕ) : rankPotential d 0 = 0 := by
  simp [rankPotential]

/-- Bounding a stopped rank bounds its harmonic potential. -/
theorem rankPotential_mono_below_dimension (d r k : ℕ) (hrk : r ≤ k) (hkd : k ≤ d) :
    rankPotential d r ≤ rankPotential d k := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hrk)
  intro j hj hjnot
  have hjk : j < k := Finset.mem_range.mp hj
  have hjd : j ≤ d := le_trans (Nat.le_of_lt hjk) hkd
  have hreal : (j : ℝ) ≤ d := by exact_mod_cast hjd
  exact div_nonneg (by norm_num) (by linarith)

/-- The finite harmonic sum has the bound used in the manuscript. -/
theorem rankPotential_le_ratio (d k : ℕ) (hkd : k ≤ d) :
    rankPotential d k ≤ (k : ℝ) / ((d : ℝ) - k + 1) := by
  have hkreal : (k : ℝ) ≤ d := by exact_mod_cast hkd
  have hden : 0 < (d : ℝ) - k + 1 := by linarith
  calc
    rankPotential d k ≤ ∑ _j ∈ Finset.range k, (1 : ℝ) / ((d : ℝ) - k + 1) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j + 1 ≤ k := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
      have hjreal : (j : ℝ) + 1 ≤ k := by exact_mod_cast hjk
      exact one_div_le_one_div_of_le hden (by linarith)
    _ = (k : ℝ) / ((d : ℝ) - k + 1) := by
      simp [div_eq_mul_inv]

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- An actual nonpositive conditional increment implies the corresponding
unconditional one-step expectation inequality. -/
theorem expected_step_le_of_conditional_increment
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (X Y : Ω → ℝ) (hX : Integrable X μ) (hY : Integrable Y μ)
    (hlocal : μ[(fun ω => Y ω - X ω) | m] ≤ᵐ[μ] (fun _ => 0)) :
    (∫ ω, Y ω ∂μ) ≤ ∫ ω, X ω ∂μ := by
  letI : MeasurableSpace Ω := mΩ
  have h := integral_mono_ae integrable_condExp (integrable_const (0 : ℝ)) hlocal
  rw [integral_condExp hm, integral_sub hY hX, integral_zero] at h
  linarith

/-- Finite-horizon telescoping of the compensated energy. No terminal energy
bound occurs among the premises. -/
theorem expected_energy_le_rankPotential_of_local_drift
    (N d k : ℕ) (hkd : k ≤ d)
    (energy : ℕ → Ω → ℝ) (rank : ℕ → Ω → ℕ)
    (past : ℕ → MeasurableSpace Ω) (hpast : ∀ t < N, past t ≤ mΩ)
    (henergy : ∀ t ≤ N, Integrable (energy t) μ)
    (hpotential : ∀ t ≤ N, Integrable (fun ω => rankPotential d (rank t ω)) μ)
    (hzero : energy 0 =ᵐ[μ] (fun _ => 0))
    (hrankzero : rank 0 =ᵐ[μ] (fun _ => 0))
    (hrankcap : ∀ᵐ ω ∂μ, rank N ω ≤ k)
    (hlocal : ∀ t < N,
      μ[(fun ω =>
        (energy (t + 1) ω - rankPotential d (rank (t + 1) ω)) -
          (energy t ω - rankPotential d (rank t ω))) | past t]
        ≤ᵐ[μ] (fun _ => 0)) :
    (∫ ω, energy N ω ∂μ) ≤ rankPotential d k := by
  let Z : ℕ → Ω → ℝ := fun t ω => energy t ω - rankPotential d (rank t ω)
  have hZ (t : ℕ) (ht : t ≤ N) : Integrable (Z t) μ :=
    (henergy t ht).sub (hpotential t ht)
  have hZzero : (∫ ω, Z 0 ω ∂μ) = 0 := by
    have hae : Z 0 =ᵐ[μ] (fun _ => 0) := by
      filter_upwards [hzero, hrankzero] with ω he hr
      simp [Z, he, hr]
    rw [integral_congr_ae hae, integral_zero]
  have hind : ∀ t ≤ N, (∫ ω, Z t ω ∂μ) ≤ 0 := by
    intro t
    induction t with
    | zero => intro ht; rw [hZzero]
    | succ t ih =>
      intro ht
      have htN : t < N := by omega
      have hstep := expected_step_le_of_conditional_increment
        (past t) (hpast t htN) (Z t) (Z (t + 1))
        (hZ t (by omega)) (hZ (t + 1) ht) (hlocal t htN)
      exact hstep.trans (ih (by omega))
  have hcomp := hind N le_rfl
  change (∫ ω, energy N ω - rankPotential d (rank N ω) ∂μ) ≤ 0 at hcomp
  rw [integral_sub (henergy N le_rfl) (hpotential N le_rfl)] at hcomp
  have hpot : (∫ ω, rankPotential d (rank N ω) ∂μ) ≤ rankPotential d k := by
    have hae : (fun ω => rankPotential d (rank N ω)) ≤ᵐ[μ]
        (fun _ => rankPotential d k) := by
      filter_upwards [hrankcap] with ω hω
      exact rankPotential_mono_below_dimension d (rank N ω) k hω hkd
    have h := integral_mono_ae (hpotential N le_rfl)
      (integrable_const (rankPotential d k)) hae
    simpa only [integral_const, probReal_univ, one_smul] using h
  linarith

omit [IsProbabilityMeasure μ] in
/-- Restricting a nonnegative stopped energy to an event cannot increase its
expectation; agreement on that event transfers the bound to the final center. -/
theorem event_energy_le_stopped_energy
    (event : Set Ω) (hevent : MeasurableSet event)
    (finalEnergy stoppedEnergy : Ω → ℝ)
    (hfinal : Integrable finalEnergy μ) (hstopped : Integrable stoppedEnergy μ)
    (hnonneg : 0 ≤ᵐ[μ] stoppedEnergy)
    (hagreement : ∀ᵐ ω ∂μ, ω ∈ event → finalEnergy ω = stoppedEnergy ω) :
    (∫ ω in event, finalEnergy ω ∂μ) ≤ ∫ ω, stoppedEnergy ω ∂μ := by
  rw [← integral_indicator hevent]
  apply integral_mono_ae (hfinal.indicator hevent) hstopped
  filter_upwards [hnonneg, hagreement] with ω hnn hag
  by_cases hω : ω ∈ event
  · simp only [indicator_of_mem hω, hag hω, le_refl]
  · simpa only [indicator_of_notMem hω, Pi.zero_apply] using hnn

#print axioms rankPotential_mono_below_dimension
#print axioms rankPotential_le_ratio
#print axioms expected_step_le_of_conditional_increment
#print axioms expected_energy_le_rankPotential_of_local_drift
#print axioms event_energy_le_stopped_energy

end
end Task006.StoppedEnergy
