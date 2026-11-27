import Nonsmooth.PosteriorKnownFunctions
import Nonsmooth.PosteriorSupportTail

open MeasureTheory ProbabilityTheory Filter
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {k : ℕ} [Nonempty (Fin k)]
  {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S]

/-- A posterior covariance bound controls every direction measurable from the history, including a.e. representatives. -/
theorem posterior_known_direction_residual_bound
    (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ)
    (hV : MemLp (fun a : Fin k → E => ∑ i, a i) 2 Q)
    (X : (Fin k → E) → E) (hX : AEStronglyMeasurable[supportTranscriptInformation p ω n] X Q)
    (hXb : ∀ a, ‖X a‖ ≤ 1) (c : ℝ)
    (hcov : ∀ᵐ h ∂Q.map (fun a => supportAugmentedTranscript p a ω n), ∀ u : E, ‖u‖ ≤ 1 →
      (∫ a : Fin k → E, ⟪u, (∑ i, a i) - ∫ b : Fin k → E, ∑ i, b i
        ∂supportPosteriorKernel Q p ω n h⟫_ℝ ^ 2 ∂supportPosteriorKernel Q p ω n h) ≤ c) :
    (∫ a : Fin k → E, ⟪(∑ i, a i) - (Q[fun b : Fin k → E => ∑ i, b i |
      supportTranscriptInformation p ω n]) a, X a⟫_ℝ ^ 2 ∂Q) ≤ c := by
  let m := supportTranscriptInformation (k := k) p ω n
  letI : MeasurableSpace (Fin k → E) := MeasurableSpace.pi
  let V : (Fin k → E) → E := fun a => ∑ i, a i
  let M := Q[V | m]
  let g : (Fin k → E) → ℝ := fun a => ⟪V a - M a, X a⟫_ℝ ^ 2
  have hm : m ≤ (MeasurableSpace.pi : MeasurableSpace (Fin k → E)) :=
    supportTranscriptInformation_le p hp ω n
  have hM : MemLp M 2 Q := hV.condExp (by norm_num)
  have hMm : AEStronglyMeasurable[m] M Q := stronglyMeasurable_condExp.aestronglyMeasurable
  have hg : Integrable g Q := (bounded_inner_memLp (hV.sub hM) (hX.mono hm) hXb).integrable_sq
  have hT : Measurable (fun a : Fin k → E => supportAugmentedTranscript p a ω n) :=
    (supportAugmentedTranscript_measurable p hp n).comp
      (measurable_id.prodMk (measurable_const (a := ω)))
  have hCE : Q[g | m] =ᵐ[Q] fun a => ∫ b, g b
      ∂supportPosteriorKernel Q p ω n (supportAugmentedTranscript p a ω n) :=
    condExp_ae_eq_integral_condDistrib_id hT hg
  have hMean : M =ᵐ[Q] fun a => ∫ b : Fin k → E, ∑ i, b i
      ∂supportPosteriorKernel Q p ω n (supportAugmentedTranscript p a ω n) :=
    supportPosteriorKernel_aggregate_mean Q p hp ω n (hV.integrable (by norm_num))
  have hb : ∀ᵐ a ∂Q, (Q[g | m]) a ≤ c := by
    filter_upwards [hCE, hMean, ae_of_ae_map hT.aemeasurable hcov,
      supportPosteriorKernel_known_function Q p hp ω n X hX,
      supportPosteriorKernel_known_function Q p hp ω n M hMm] with a hce hmean hc hx hma
    rw [hce]
    have he : (∫ b, g b ∂supportPosteriorKernel Q p ω n (supportAugmentedTranscript p a ω n)) =
        ∫ b : Fin k → E, ⟪X a, (∑ i, b i) - ∫ z : Fin k → E, ∑ i, z i
          ∂supportPosteriorKernel Q p ω n (supportAugmentedTranscript p a ω n)⟫_ℝ ^ 2
          ∂supportPosteriorKernel Q p ω n (supportAugmentedTranscript p a ω n) := by
      apply integral_congr_ae
      filter_upwards [hx, hma] with b hxb hmb
      dsimp only [g, V]
      rw [hxb, hmb, hmean, real_inner_comm]
    rw [he]
    exact hc (X a) (hXb a)
  change (∫ a, g a ∂Q) ≤ c
  calc
    _ = ∫ a, (Q[g | m]) a ∂Q := (integral_condExp hm).symm
    _ ≤ ∫ _ : Fin k → E, c ∂Q := integral_mono_ae integrable_condExp (integrable_const c) hb
    _ = c := by simp

end
end Nonsmooth
