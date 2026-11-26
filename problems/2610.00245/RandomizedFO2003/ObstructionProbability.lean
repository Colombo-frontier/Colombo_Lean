import RandomizedFO2003.GenieProbability
import RandomizedFO2003.CascadeObstruction

namespace RandomizedFO2003.FiniteSpectralDesign

open MeasureTheory SpectralCoordinates Cascade Rotations Spherical
open scoped BigOperators ENNReal

variable {m : ℕ} {γ L : ℝ} (S : FiniteSpectralDesign m γ L (1 / (16 * γ)))

/-- Both probability budgets hold for the same original sphere/Haar law,
with a dimension chosen before every algorithm and private seed law. -/
theorem choose_terminal_budgets (hγ : 0 < γ) {h : ℝ} (hh : 0 < h)
    (N T : ℕ) (hT : T < (N + 1) * m) :
    ∃ K : Fin S.size → ℕ, 0 < ∑ j, K j ∧
      ∀ (Seed : Type) [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
        (A : Model.Algorithm ((N + 1) * ∑ j, K j) Seed),
        Measure.pi (fun _ : Fin (N + 1) => sphereLaw (BlockSpace K)) (S.cascadeGoodEvent K N)ᶜ ≤
          (1 / 6 : ℝ≥0∞) ∧
        ((S.cascadeParameterLaw K N).prod ν) (S.terminalFlatEvent K N h A T (Fin.last N))ᶜ ≤
          (1 / 6 : ℝ≥0∞) := by
  obtain ⟨K, _hK, _hN, _hdim, htotal, hunit, hprob⟩ :=
    S.choose_genie_multiplicities hγ hh (show (0 : ℝ) < 1 / 6 by norm_num) N T 0 0
  refine ⟨K, htotal, ?_⟩
  intro Seed _ ν _ A
  have hb : ∑ i : Fin (N + 1), ((S.cascadeParameterLaw K N).prod ν)
      (S.censoredGenieGoodEvent K N h A T i)ᶜ ≤ (1 / 6 : ℝ≥0∞) := by
    simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 6),
      ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using hprob Seed ν A
  exact ⟨(S.spectral_bad_probability_le_genie_bad K N h hunit ν A T).trans hb,
    (S.terminal_bad_probability_le_genie_bad K N h ν A T hT).trans hb⟩

end RandomizedFO2003.FiniteSpectralDesign
