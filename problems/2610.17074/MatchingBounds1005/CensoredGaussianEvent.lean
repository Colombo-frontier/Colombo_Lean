import MatchingBounds1005.CensoredGaussianProcess
import MatchingBounds1005.ProbabilityMoment
import MatchingBounds1005.EventTransfer

/-!
# High-probability geometry in the actual Gaussian comparison

The rare bad-geometry contribution is integrated under the reference law.
The resulting bound applies to the true static experiment via the proved
change-of-measure inequality. Fixed-objective first-exit coupling is a
separate layer.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

namespace MatchingBounds1005.CensoredGaussianEvent
open CensoredGaussianProcess SequentialPosterior

variable {Ω : Type*} [MeasurableSpace Ω] {d T : ℕ}

theorem transcript_klDiv_le_good_event (A : CensoredProtocol Ω d T) {σ : ℝ} (hσ : σ ≠ 0)
    (ν₀ : Measure Ω) [IsProbabilityMeasure ν₀] (C : ℕ → ℝ≥0)
    (hc : ∀ n h, ‖hidden A n h‖ ^ 2 / (2 * σ ^ 2) ≤ C n)
    (n : ℕ) (G : Set (History Ω T n)) (hG : MeasurableSet G)
    (goodCap globalCap ζ : ℝ) (hgoodCap : 0 ≤ goodCap) (hglobalCap : 0 ≤ globalCap)
    (hgood : ∀ h ∈ G, SeededKernelKL.cumulativeCost (energyCost A σ) n h ≤ goodCap)
    (hglobal : ∀ h, SeededKernelKL.cumulativeCost (energyCost A σ) n h ≤ globalCap)
    (hfail : (referenceLaw A σ ν₀ n).real Gᶜ ≤ ζ) :
    klDiv (referenceLaw A σ ν₀ n) (trueLaw A σ ν₀ n) ≤
      ENNReal.ofReal (goodCap + ζ * globalCap) := by
  rw [transcript_klDiv A hσ ν₀ C hc n]
  apply ENNReal.ofReal_le_ofReal
  exact ProbabilityMoment.integral_le_good_add_bad (referenceLaw A σ ν₀ n) _
    (cumulativeCost_integrable A hσ ν₀ C hc n) G hG goodCap globalCap ζ
    hgoodCap hglobalCap hgood hglobal hfail

/-- Actual reference-to-true transfer for the complement of the geometry
event, using a proved entropy inequality rather than a postulated Pinsker bound. -/
theorem true_bad_probability (A : CensoredProtocol Ω d T) {σ : ℝ} (hσ : σ ≠ 0)
    (ν₀ : Measure Ω) [IsProbabilityMeasure ν₀] (C : ℕ → ℝ≥0)
    (hc : ∀ n h, ‖hidden A n h‖ ^ 2 / (2 * σ ^ 2) ≤ C n)
    (n : ℕ) (G : Set (History Ω T n)) (hG : MeasurableSet G)
    (goodCap globalCap ζ : ℝ) (hgoodCap : 0 ≤ goodCap) (hglobalCap : 0 ≤ globalCap)
    (hgood : ∀ h ∈ G, SeededKernelKL.cumulativeCost (energyCost A σ) n h ≤ goodCap)
    (hglobal : ∀ h, SeededKernelKL.cumulativeCost (energyCost A σ) n h ≤ globalCap)
    (hfail : (referenceLaw A σ ν₀ n).real Gᶜ ≤ ζ) :
    (trueLaw A σ ν₀ n).real Gᶜ ≤
      (4 / 3 : ℝ) * (goodCap + ζ * globalCap + Real.log 4 * ζ) := by
  have hb := transcript_klDiv_le_good_event A hσ ν₀ C hc n G hG goodCap globalCap ζ
    hgoodCap hglobalCap hgood hglobal hfail
  have hfinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  have hζ : 0 ≤ ζ := (measureReal_nonneg (μ := referenceLaw A σ ν₀ n) (s := Gᶜ)).trans hfail
  have hcap : 0 ≤ goodCap + ζ * globalCap := add_nonneg hgoodCap (mul_nonneg hζ hglobalCap)
  have hreal : (klDiv (referenceLaw A σ ν₀ n) (trueLaw A σ ν₀ n)).toReal ≤ goodCap + ζ * globalCap := by
    simpa only [ENNReal.toReal_ofReal hcap] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  exact EventTransfer.probability_event_le_of_bounds Gᶜ hG.compl hfinite hreal hfail

end MatchingBounds1005.CensoredGaussianEvent
