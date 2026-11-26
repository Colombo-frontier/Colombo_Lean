import Matvec.SourceEstimator
import Matvec.MaximumAmplification
import Mathlib.Analysis.SpecificLimits.Basic

/-! Arbitrarily reliable spectral estimation with explicit repetition counts. -/

namespace Matvec

open MeasureTheory
noncomputable section

theorem sourceStartProbability_le_half : sourceStartProbability ≤ 1 / 2 := by
  have h : RandomStart.intervalMass ≤ 1 :=
    (measureReal_mono (μ := ProbabilityTheory.gaussianReal 0 1) (Set.subset_univ _)).trans_eq
      measureReal_univ_eq_one
  change RandomStart.intervalMass / 2 ≤ 1 / 2
  linarith

/-- Number of additional verified repetitions; the verification executes R+1
base runs. The extra 1 in the denominator handles even a zero correction count. -/
def sourceVerificationLength (θ : ℝ) (q J : ℕ) : ℕ :=
  refinementLength (θ / ((q : ℝ) * J + 1))

theorem sourceVerificationLength_bounds (θ : ℝ) (hθ : 0 < θ) (q J : ℕ) :
    (sourceVerificationLength θ q J : ℝ) <
      2 * |Real.log (θ / ((q : ℝ) * J + 1))| + 1 ∧
    (q : ℝ) * J * (2 / 5 : ℝ) ^ (sourceVerificationLength θ q J + 1) ≤ θ := by
  have hden : 0 < (q : ℝ) * J + 1 := by positivity
  have hh := refinementLength_bounds (θ / ((q : ℝ) * J + 1)) (div_pos hθ hden)
  refine ⟨hh.1, ?_⟩
  have hp : (2 / 5 : ℝ) ^ (sourceVerificationLength θ q J + 1) ≤
      (1 / 2 : ℝ) ^ sourceVerificationLength θ q J := by
    calc
      _ = (2 / 5 : ℝ) ^ sourceVerificationLength θ q J * (2 / 5) := pow_succ _ _
      _ ≤ (2 / 5 : ℝ) ^ sourceVerificationLength θ q J :=
        mul_le_of_le_one_right (by positivity) (by norm_num)
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  calc
    _ ≤ (q : ℝ) * J * (θ / ((q : ℝ) * J + 1)) :=
      mul_le_mul_of_nonneg_left (hp.trans hh.2) (by positivity)
    _ ≤ θ := by
      apply (le_of_mul_le_mul_right ?_ hden)
      field_simp
      nlinarith

theorem exists_source_start_repetitions (ε : ℝ) (hε : 0 < ε) :
    ∃ S : ℕ, (1 - sourceStartProbability / 2) ^ (S + 1) ≤ ε / 2 := by
  have hp := sourceStart_constants_pos.2
  have hpupper := sourceStartProbability_le_half
  obtain ⟨S, hS⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 2 by positivity)
    (show 1 - sourceStartProbability / 2 < 1 by linarith)
  refine ⟨S, ?_⟩
  calc
    _ = (1 - sourceStartProbability / 2) ^ S * (1 - sourceStartProbability / 2) := pow_succ _ _
    _ ≤ (1 - sourceStartProbability / 2) ^ S :=
      mul_le_of_le_one_right (pow_nonneg (by linarith) _) (by linarith)
    _ ≤ ε / 2 := hS.le

variable {E Seed : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Seed]

instance sourceEstimatorLaw_probability (μ : Measure Seed) [IsProbabilityMeasure μ] (R : ℕ) :
    IsProbabilityMeasure (sourceEstimatorLaw (E := E) μ R) := by
  unfold sourceEstimatorLaw
  infer_instance

/-- For each requested fixed confidence, a constant number of starts suffices.
The base-solver verification count is explicit and logarithmic in qJ. -/
theorem sourceEstimator_reliable_of_start_count (ε : ℝ) (hε : 0 < ε) (S : ℕ)
    (hS : (1 - sourceStartProbability / 2) ^ (S + 1) ≤ ε / 2) :
    ∀ (μ : Measure Seed) [IsProbabilityMeasure μ]
      (H M : E →L[ℝ] E), H.toLinearMap.IsSymmetric →
      (∀ x, H (M x) = x) → (∀ x, M (H x) = x) →
      ∀ (base : E → Seed → E),
      Measurable (fun p : E × Seed => base p.1 p.2) →
      (∀ r, 3 / 5 ≤ μ.real {seed | ‖H (base r seed) - r‖ ≤ ‖r‖ / 2}) →
      2 ≤ Module.finrank ℝ E →
      let d := Module.finrank ℝ E
      let q := inversePowerLengthFor sourceStartComponent d
      let J := refinementLength (inversePowerAccuracyFor sourceStartComponent d)
      let θ := min (sourceStartProbability / 2) (ε / (2 * (S + 1 : ℝ)))
      let R := sourceVerificationLength θ q J
      1 - ε ≤ (Measure.pi (fun _ : Fin (S + 1) => sourceEstimatorLaw (E := E) μ R)).real
        {seeds | ‖M‖ / 2 ≤ repeatedMaximum (sourceEstimator H base R) S seeds ∧
          repeatedMaximum (sourceEstimator H base R) S seeds ≤ 2 * ‖M‖} := by
  intro μ inst H M hH hHM hMH base hbase hsuccess hd
  dsimp only
  let q := inversePowerLengthFor sourceStartComponent (Module.finrank ℝ E)
  let J := refinementLength (inversePowerAccuracyFor sourceStartComponent (Module.finrank ℝ E))
  let θ := min (sourceStartProbability / 2) (ε / (2 * (S + 1 : ℝ)))
  let R := sourceVerificationLength θ q J
  have hθ : 0 < θ := lt_min (half_pos sourceStart_constants_pos.2) (by positivity)
  have hbudget := (sourceVerificationLength_bounds θ hθ q J).2
  have hs := sourceEstimator_probability μ H M hH hHM hMH base hbase hsuccess hd R
  have hlower : sourceStartProbability / 2 ≤ (sourceEstimatorLaw (E := E) μ R).real
      {s | ‖M‖ / 2 ≤ sourceEstimator H base R s ∧ sourceEstimator H base R s ≤ 2 * ‖M‖} := by
    have ht : θ ≤ sourceStartProbability / 2 := min_le_left _ _
    have hp := hs.1
    change sourceStartProbability - (q : ℝ) * J * (2 / 5 : ℝ) ^ (R + 1) ≤ _ at hp
    change (q : ℝ) * J * (2 / 5 : ℝ) ^ (R + 1) ≤ θ at hbudget
    linarith
  have hupper : (sourceEstimatorLaw (E := E) μ R).real
      {s | 2 * ‖M‖ < sourceEstimator H base R s} ≤ θ := hs.2.trans hbudget
  have hmax := repeatedMaximum_success (sourceEstimatorLaw (E := E) μ R)
    (sourceEstimator H base R) (measurable_sourceEstimator H base hbase R) S
      (‖M‖ / 2) (2 * ‖M‖) (sourceStartProbability / 2) θ hlower hupper
  have hbudget2 : (S + 1 : ℝ) * θ ≤ ε / 2 := by
    calc
      _ ≤ (S + 1 : ℝ) * (ε / (2 * (S + 1 : ℝ))) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = ε / 2 := by field_simp; ring
  apply le_trans ?_ hmax
  linarith

theorem sourceEstimator_arbitrarily_reliable (ε : ℝ) (hε : 0 < ε) :
    ∃ S : ℕ, ∀ (μ : Measure Seed) [IsProbabilityMeasure μ]
      (H M : E →L[ℝ] E), H.toLinearMap.IsSymmetric →
      (∀ x, H (M x) = x) → (∀ x, M (H x) = x) →
      ∀ (base : E → Seed → E),
      Measurable (fun p : E × Seed => base p.1 p.2) →
      (∀ r, 3 / 5 ≤ μ.real {seed | ‖H (base r seed) - r‖ ≤ ‖r‖ / 2}) →
      2 ≤ Module.finrank ℝ E →
      let d := Module.finrank ℝ E
      let q := inversePowerLengthFor sourceStartComponent d
      let J := refinementLength (inversePowerAccuracyFor sourceStartComponent d)
      let θ := min (sourceStartProbability / 2) (ε / (2 * (S + 1 : ℝ)))
      let R := sourceVerificationLength θ q J
      1 - ε ≤ (Measure.pi (fun _ : Fin (S + 1) => sourceEstimatorLaw (E := E) μ R)).real
        {seeds | ‖M‖ / 2 ≤ repeatedMaximum (sourceEstimator H base R) S seeds ∧
          repeatedMaximum (sourceEstimator H base R) S seeds ≤ 2 * ‖M‖} := by
  obtain ⟨S, hS⟩ := exists_source_start_repetitions ε hε
  exact ⟨S, sourceEstimator_reliable_of_start_count ε hε S hS⟩

end
end Matvec
