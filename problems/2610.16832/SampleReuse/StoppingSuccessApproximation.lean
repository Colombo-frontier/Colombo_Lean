import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

open MeasureTheory
open scoped ENNReal
namespace SampleReuse

/-- Both hypotheses have one common finite horizon, without any bound on
the stopping time's expectation and without an almost-sure termination premise. -/
theorem binary_success_finite_horizon {Ω : Type*} [MeasurableSpace Ω]
    (μ : Bool → Measure Ω) [∀ θ, IsProbabilityMeasure (μ θ)]
    (E : Bool → ℕ → Set Ω) (hmono : ∀ θ, Monotone (E θ))
    (hsuccess : ∀ θ, (2/3:ℝ) ≤ (μ θ).real (⋃ n, E θ n)) :
    ∃ N, ∀ θ, (3/5:ℝ) ≤ (μ θ).real (E θ N) := by
  have hex (θ : Bool) : ∃ n, (3/5:ℝ) ≤ (μ θ).real (E θ n) := by
    have hl : ENNReal.ofReal (2/3:ℝ) ≤ μ θ (⋃ n, E θ n) :=
      (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr (hsuccess θ)
    have ht : ENNReal.ofReal (3/5:ℝ) < μ θ (⋃ n, E θ n) :=
      lt_of_lt_of_le (by norm_num) hl
    rw [(hmono θ).measure_iUnion] at ht
    obtain ⟨n,hn⟩ := lt_iSup_iff.mp ht
    exact ⟨n,(ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hn.le⟩
  obtain ⟨nf,hf⟩ := hex false
  obtain ⟨nt,ht⟩ := hex true
  refine ⟨max nf nt,?_⟩
  intro θ
  cases θ with
  | false => exact hf.trans (measureReal_mono (hmono false (le_max_left _ _)))
  | true => exact ht.trans (measureReal_mono (hmono true (le_max_right _ _)))

end SampleReuse
