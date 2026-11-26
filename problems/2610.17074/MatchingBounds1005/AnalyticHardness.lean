import MatchingBounds1005.AnalyticOracle
import MatchingBounds1005.ConditionedFamily

/-! Conditioning the concrete fixed family after the unconditioned first-exit
estimate. The all-policy first-exit estimate remains the explicit probabilistic
premise; it is not asserted by this module. -/
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace MatchingBounds1005.AnalyticFamily
open EpsilonCalibration TensorGeometry

instance rotation_standardBorel (d : ℕ) :
    StandardBorelSpace (RandomizedFO2003.Rotations.Rotation (Vec d)) := by
  letI : PolishSpace (RandomizedFO2003.Rotations.Rotation (Vec d)) :=
    (RandomizedFO2003.Rotations.rotation_isClosed (Vec d)).polishSpace
  infer_instance

theorem good_mass_lower (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hs : t ≤ parameterThreshold p) (K : ℕ) :
    (1 / 5 : ℝ) ≤ (sampleLaw p t K).real (Good p t K) := by
  have hdR : (1 : ℝ) ≤ dimension p t K := by
    exact_mod_cast dimension_pos p t ht hs K
  have he : (5 : ℝ) ≤ Real.exp (4 * dimension p t K) := by
    have h := Real.add_one_le_exp (4 * (dimension p t K : ℝ))
    linarith
  have he' : Real.exp (-4 * dimension p t K) ≤ 1 / 5 := by
    rw [show -4 * (dimension p t K : ℝ) = -(4 * dimension p t K) by ring, Real.exp_neg,
      ← one_div]
    exact (div_le_iff₀ (Real.exp_pos _)).mpr (by linarith)
  have hg := good_probability p t K
  linarith

def firstExitEvent {Seed : Type} [MeasurableSpace Seed]
    (p : ℕ) (t : ℝ) (ht : 0 < t) (hs : t ≤ parameterThreshold p) (K : ℕ)
    (A : Model.Algorithm (dimension p t K) Seed)
    (S : ℕ → Finset (Fin (phaseCount (amplitudeConstant p) t - 1 + 1))) (T : ℕ) :
    Set (Sample p t K × Seed) :=
  {z | z.2 ∈ Model.FirstExit (sampledReply p t ht hs K z.1 A S)
    (querySafe p t ht hs K z.1 A S) (outputSafe p t ht hs K z.1 A T)}

theorem conditioned_hardDistribution_of_firstExit
    (p : ℕ) (hp : 1 ≤ p) (t : ℝ) (ht : 0 < t) (hs : t ≤ parameterThreshold p) (K T : ℕ)
    (S : ℕ → Finset (Fin (phaseCount (amplitudeConstant p) t - 1 + 1)))
    (hbound : ∀ (Seed : Type) [MeasurableSpace Seed] [StandardBorelSpace Seed]
      (ν : Measure Seed) [IsProbabilityMeasure ν] (A : Model.Algorithm (dimension p t K) Seed),
      ((sampleLaw p t K).prod ν).real (firstExitEvent p t ht hs K A S T) ≤ 1 / 15) :
    Model.HardDistribution p (dimension p t K) T (t ^ 3) := by
  have hmass := good_mass_lower p t ht hs K
  have hpos : 0 < (sampleLaw p t K).real (Good p t K) := lt_of_lt_of_le (by norm_num) hmass
  apply Model.hardDistribution_of_conditioning (t ^ 3) (sampleLaw p t K)
    (sampledObjective p t ht hs K) (Good p t K) (good_measurable p t K)
  · intro hz
    simp only [Measure.real, hz, ENNReal.toReal_zero] at hpos
    exact lt_irrefl _ hpos
  · exact sampledObjective_oracle_measurable p t ht hs K
  · exact sampledObjective_inFunctionClass p t ht hs K
  · intro Seed _ _ ν _ A
    have hsubset : {z : Sample p t K × Seed |
        z.2 ∈ Model.Success A (sampledObjective p t ht hs K z.1) (t ^ 3) T} ∩
          (Good p t K ×ˢ Set.univ) ⊆ firstExitEvent p t ht hs K A S T := by
      intro z hz
      exact sampled_success_subset_firstExit p hp t ht hs K z.1 hz.2.1 A S T hz.1
    have hnum := (measureReal_mono hsubset).trans (hbound Seed ν A)
    apply (div_le_iff₀ hpos).mpr
    nlinarith

end MatchingBounds1005.AnalyticFamily
