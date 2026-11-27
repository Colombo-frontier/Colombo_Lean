import Nonsmooth.SupportTranscriptInfo
import Nonsmooth.SupportAffineGeometry
import Mathlib.Probability.Kernel.CondDistrib

open MeasureTheory ProbabilityTheory Filter
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {k : ℕ} [Nonempty (Fin k)] {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S]

/-- The actual regular conditional distribution of all rows given the augmented
history. Its existence does not assert row independence or a Gaussian slice density. -/
def supportPosteriorKernel (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (p : Policy Ω S E) (ω : Ω) (n : ℕ) : Kernel (SupportHistory E k n) (Fin k → E) :=
  condDistrib id (fun a => supportAugmentedTranscript p a ω n) Q

instance supportPosteriorKernel_isMarkov (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (p : Policy Ω S E) (ω : Ω) (n : ℕ) : IsMarkovKernel (supportPosteriorKernel Q p ω n) := by
  unfold supportPosteriorKernel
  infer_instance

theorem supportPosteriorKernel_disintegrates (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (p : Policy Ω S E) (ω : Ω) (n : ℕ) :
    (Q.map (fun a => supportAugmentedTranscript p a ω n)) ⊗ₘ supportPosteriorKernel Q p ω n =
      Q.map (fun a => (supportAugmentedTranscript p a ω n, a)) :=
  compProd_map_condDistrib aemeasurable_id

theorem supportPosteriorKernel_fiber (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ) :
    ∀ᵐ h ∂Q.map (fun a => supportAugmentedTranscript p a ω n),
      ∀ᵐ a ∂supportPosteriorKernel Q p ω n h, supportAugmentedTranscript p a ω n = h := by
  have hF : Measurable (fun a : Fin k → E => supportAugmentedTranscript p a ω n) :=
    (supportAugmentedTranscript_measurable p hp n).comp (measurable_id.prodMk measurable_const)
  have hg : MeasurableSet {z : SupportHistory E k n × (Fin k → E) |
      supportAugmentedTranscript p z.2 ω n = z.1} :=
    (hF.comp measurable_snd).stronglyMeasurable.measurableSet_eq_fun measurable_fst.stronglyMeasurable
  have hmap : ∀ᵐ z ∂Q.map (fun a => (supportAugmentedTranscript p a ω n, a)),
      supportAugmentedTranscript p z.2 ω n = z.1 :=
    (ae_map_iff (hF.prodMk measurable_id).aemeasurable hg).mpr (Eventually.of_forall (fun _ => rfl))
  rw [← supportPosteriorKernel_disintegrates Q p ω n] at hmap
  exact (Measure.ae_compProd_iff hg).mp hmap

theorem supportPosteriorKernel_row_cells (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ) :
    ∀ᵐ h ∂Q.map (fun a => supportAugmentedTranscript p a ω n),
      supportHistoryConsistent p ω n h ∧
        ∀ᵐ a ∂supportPosteriorKernel Q p ω n h, ∀ i, a i ∈ supportHistoryCell n h i := by
  filter_upwards [supportPosteriorKernel_fiber Q p hp ω n] with h hh
  have hgood : ∀ᵐ a ∂supportPosteriorKernel Q p ω n h,
      supportHistoryConsistent p ω n h ∧ ∀ i, a i ∈ supportHistoryCell n h i :=
    hh.mono (fun a ha => (supportAugmentedTranscript_fiber p a ω n h).mp ha)
  obtain ⟨a, ha⟩ := hgood.exists
  exact ⟨ha.1, hgood.mono (fun _ hb => hb.2)⟩

theorem supportPosteriorKernel_affine_support (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ) :
    ∀ᵐ h ∂Q.map (fun a => supportAugmentedTranscript p a ω n),
      ∃ b : Fin k → E, (∀ i, b i ∈ supportHistoryCell n h i) ∧
        ∀ᵐ a ∂supportPosteriorKernel Q p ω n h,
          ∀ i, a i - b i ∈ LinearMap.ker (supportWinningMap h i) := by
  filter_upwards [supportPosteriorKernel_row_cells Q p hp ω n] with h hh
  obtain ⟨b, hb⟩ := hh.2.exists
  exact ⟨b, hb, hh.2.mono (fun a ha i => supportHistoryCell_kernel_difference h i (hb i) (ha i))⟩

theorem supportPosteriorKernel_aggregate_mean (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ)
    (hi : Integrable (fun a : Fin k → E => ∑ i, a i) Q) :
    Q[fun a => ∑ i, a i | supportTranscriptInformation p ω n] =ᵐ[Q]
      fun a => ∫ b, ∑ i, b i ∂supportPosteriorKernel Q p ω n (supportAugmentedTranscript p a ω n) := by
  have hF : Measurable (fun a : Fin k → E => supportAugmentedTranscript p a ω n) :=
    (supportAugmentedTranscript_measurable p hp n).comp (measurable_id.prodMk measurable_const)
  have hs : StronglyMeasurable (fun a : Fin k → E => ∑ i, a i) :=
    (continuous_finsetSum _ (fun i _ => continuous_apply i)).stronglyMeasurable
  exact condExp_ae_eq_integral_condDistrib hF aemeasurable_id hs hi

end
end Nonsmooth
