import Nonsmooth.GaussianSupportPosterior
import Nonsmooth.PosteriorEnergy

open MeasureTheory ProbabilityTheory Filter
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  {k : ℕ} [Nonempty (Fin k)] {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S]

theorem gaussianAmbientRows_aggregate_memLp :
    MemLp (fun a : Fin k → E => ∑ i, a i) 2 (Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)) :=
  memLp_finset_sum _ (fun i _ => gaussianAmbientRows_coordinate_memLp i)

def gaussianSupportMean (p : Policy Ω S E) (ω : Ω) (n : ℕ) : (Fin k → E) → E :=
  (Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E))[
    fun a => ∑ i, a i | supportTranscriptInformation p ω n]

theorem gaussianSupportMean_initial (p : Policy Ω S E) (ω : Ω) :
    gaussianSupportMean (k := k) p ω 0 = fun _ => (0 : E) :=
  gaussianSupportPosterior_initial_mean p ω

/-- The martingale accumulation step is proved for the actual Gaussian prior and
actual transcript. The logarithmic one-observation estimate remains an explicit premise. -/
theorem gaussian_support_energy_from_steps (p : Policy Ω S E) (hp : p.IsMeasurable)
    (ω : Ω) (T : ℕ) {C : ℝ}
    (hstep : ∀ n < T, (∫ a : Fin k → E,
      ‖gaussianSupportMean p ω (n + 1) a - gaussianSupportMean p ω n a‖ ^ 2
        ∂Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)) ≤
          C * Real.log (Real.exp 1 * k) / (Module.finrank ℝ E : ℝ)) :
    (∫ a : Fin k → E, ‖gaussianSupportMean p ω T a‖ ^ 2
      ∂Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)) ≤
        C * (T : ℝ) * Real.log (Real.exp 1 * k) / (Module.finrank ℝ E : ℝ) := by
  have hzero : (∫ a : Fin k → E, ‖gaussianSupportMean p ω 0 a‖ ^ 2
      ∂Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)) = 0 := by
    simp only [gaussianSupportMean_initial, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, integral_zero]
  have h := conditional_mean_energy_from_increments (supportTranscriptInformation p ω)
    (supportTranscriptInformation_mono p ω) (supportTranscriptInformation_le p hp ω)
    (gaussianAmbientRows_aggregate_memLp (E := E) (k := k)) hzero T hstep
  convert! h using 1 <;> first | rfl | ring

end
end Nonsmooth
