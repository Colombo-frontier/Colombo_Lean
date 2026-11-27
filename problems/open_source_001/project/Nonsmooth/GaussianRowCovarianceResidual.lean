import Nonsmooth.PosteriorDirectionalBound

open MeasureTheory ProbabilityTheory Filter
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  {k : ℕ} [Nonempty (Fin k)] {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S]

/-- A coarse unconditional bound valid even for directions selected from the full adaptive history. -/
theorem gaussianSupportMean_known_direction_residual_coarse
    (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ)
    (X : (Fin k → E) → E)
    (hX : AEStronglyMeasurable[supportTranscriptInformation p ω n] X
      (Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)))
    (hXb : ∀ a, ‖X a‖ ≤ 1) :
    (∫ a : Fin k → E, ⟪(∑ i, a i) - gaussianSupportMean p ω n a, X a⟫_ℝ ^ 2
      ∂Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)) ≤ 4 * (k : ℝ) := by
  apply posterior_known_direction_residual_bound _ p hp ω n
    gaussianAmbientRows_aggregate_memLp X hX hXb
  filter_upwards [gaussianSupportPosterior_centered_second_le_coarse (k := k) p hp ω n] with h hh u hu
  apply (hh u).trans
  have hs : ‖u‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg u]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

/-- The sharp residual branch reduces to a pointwise one-row posterior covariance bound.
The covariance hypothesis is explicit and remains to be proved from the Gaussian slice geometry. -/
theorem gaussianSupportMean_known_direction_residual_of_row_covariance
    (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ)
    (X : (Fin k → E) → E)
    (hX : AEStronglyMeasurable[supportTranscriptInformation p ω n] X
      (Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)))
    (hXb : ∀ a, ‖X a‖ ≤ 1)
    (hcov : ∀ᵐ h ∂(Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)).map
      (fun a => supportAugmentedTranscript p a ω n), ∀ (u : E) (i : Fin k),
      variance (fun a : Fin k → E => ⟪u, a i⟫_ℝ)
        (supportPosteriorKernel (Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)) p ω n h) ≤
          ‖u‖ ^ 2 / (Module.finrank ℝ E : ℝ)) :
    (∫ a : Fin k → E, ⟪(∑ i, a i) - gaussianSupportMean p ω n a, X a⟫_ℝ ^ 2
      ∂Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)) ≤
      (k : ℝ) / (Module.finrank ℝ E : ℝ) := by
  apply posterior_known_direction_residual_bound _ p hp ω n
    gaussianAmbientRows_aggregate_memLp X hX hXb
  filter_upwards [gaussianSupportPosterior_centered_second (k := k) p hp ω n, hcov] with h he hv u hu
  rw [he u]
  have hs : ‖u‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg u]
  have hc : 0 ≤ (k : ℝ) / (Module.finrank ℝ E : ℝ) := div_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ _ : Fin k, ‖u‖ ^ 2 / (Module.finrank ℝ E : ℝ) := Finset.sum_le_sum (fun i _ => hv u i)
    _ = ((k : ℝ) / (Module.finrank ℝ E : ℝ)) * ‖u‖ ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ ≤ (k : ℝ) / (Module.finrank ℝ E : ℝ) := by nlinarith

end
end Nonsmooth
