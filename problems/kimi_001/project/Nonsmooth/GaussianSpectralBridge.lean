import Nonsmooth.SupportGram
import Nonsmooth.GaussianAmbientRowLaw
import Nonsmooth.ConditioningProbability

open MeasureTheory ProbabilityTheory Metric Function Filter
open scoped ENNReal InnerProductSpace Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

def supportGramGood (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) : Set (Fin k → E) :=
  {a | ∀ c : Fin k → ℝ, (1 / 4 : ℝ) * (∑ i, (c i) ^ 2) ≤ ‖∑ i, c i • a i‖ ^ 2}

theorem supportGramGood_closed (k : ℕ) : IsClosed (supportGramGood E k) := by
  have he : supportGramGood E k = ⋂ c : Fin k → ℝ,
      {a : Fin k → E | (1 / 4 : ℝ) * (∑ i, (c i) ^ 2) ≤ ‖∑ i, c i • a i‖ ^ 2} := by
    ext a; simp only [supportGramGood, Set.mem_setOf_eq, Set.mem_iInter]
  rw [he]
  apply isClosed_iInter
  intro c
  exact isClosed_le continuous_const
    ((continuous_finsetSum _ (fun i _ => continuous_const.smul (continuous_apply i))).norm.pow 2)

def gaussianScaleRows (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (k : ℕ) (b : Fin k → E) : Fin k → E :=
  fun i => (Real.sqrt (Module.finrank ℝ E))⁻¹ • b i

theorem gaussianScaleRows_measurable (k : ℕ) : Measurable (gaussianScaleRows E k) :=
  measurable_pi_lambda _ (fun i => measurable_const.smul (measurable_pi_apply i))

theorem gaussianSupportPrior_ambient_map (k : ℕ) :
    Measure.map (fun a : BoundedSupportRows E (Fin k) => fun i => (a i).val) (gaussianSupportPrior E k) =
      Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E) := by
  have hp := measurePreserving_pi (fun _ : Fin k => gaussianSupportRowLaw E)
    (fun _ : Fin k => gaussianAmbientRowLaw E)
    (fun _ => show MeasurePreserving (Subtype.val : Feasible E 2 → E)
      (gaussianSupportRowLaw E) (gaussianAmbientRowLaw E) from ⟨measurable_subtype_coe, rfl⟩)
  exact hp.map_eq

theorem gaussianScaledProduct_map (k : ℕ) :
    Measure.map (gaussianScaleRows E k) (Measure.pi (fun _ : Fin k => truncatedGaussianLaw E)) =
      Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E) := by
  have hm : Measurable (fun z : E => (Real.sqrt (Module.finrank ℝ E))⁻¹ • z) :=
    measurable_const.smul measurable_id
  have hrow : MeasurePreserving (fun z : E => (Real.sqrt (Module.finrank ℝ E))⁻¹ • z)
      (truncatedGaussianLaw E) (gaussianAmbientRowLaw E) :=
    ⟨hm, gaussianSupportRowLaw_map.symm⟩
  exact (measurePreserving_pi (fun _ : Fin k => truncatedGaussianLaw E)
    (fun _ : Fin k => gaussianAmbientRowLaw E) (fun _ => hrow)).map_eq

theorem gaussianSupportPrior_gram_event_of_spectral_probability {k : ℕ}
    (hk : (k : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 16)
    (hraw : 15 / 16 ≤ (Measure.pi (fun _ : Fin k => euclideanGaussianLaw E)).real
      ((gaussianScaleRows E k) ⁻¹' supportGramGood E k)) :
    7 / 8 ≤ (gaussianSupportPrior E k).real
      {a : BoundedSupportRows E (Fin k) | (fun i => (a i).val) ∈ supportGramGood E k} := by
  have hs := (supportGramGood_closed (E := E) k).measurableSet
  have ht := gaussian_truncated_product_event hk _ ((gaussianScaleRows_measurable k) hs) hraw
  have hm : Measurable (fun a : BoundedSupportRows E (Fin k) => fun i => (a i).val) :=
    measurable_pi_lambda _ (fun i => measurable_subtype_coe.comp (measurable_pi_apply i))
  have he : Measure.map (fun a : BoundedSupportRows E (Fin k) => fun i => (a i).val) (gaussianSupportPrior E k) =
      Measure.map (gaussianScaleRows E k) (Measure.pi (fun _ : Fin k => truncatedGaussianLaw E)) :=
    (gaussianSupportPrior_ambient_map k).trans (gaussianScaledProduct_map k).symm
  have hprob := congrArg (fun μ : Measure (Fin k → E) => μ.real (supportGramGood E k)) he
  try dsimp only at hprob
  rw [map_measureReal_apply hm hs, map_measureReal_apply (gaussianScaleRows_measurable k) hs] at hprob
  exact ht.trans_eq hprob.symm

/-- Full transfer of a 15/16 unconditioned Gaussian Gram event to the original
7/8 negative-optimum event. The unconditioned spectral probability is an explicit
premise of this reduction and remains a separate proof obligation. -/
theorem gaussianSupportPrior_negative_of_spectral_probability {k : ℕ} (hk : 0 < k)
    (hkd : (k : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 16)
    (hraw : 15 / 16 ≤ (Measure.pi (fun _ : Fin k => euclideanGaussianLaw E)).real
      ((gaussianScaleRows E k) ⁻¹' supportGramGood E k)) :
    letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    7 / 8 ≤ (gaussianSupportPrior E k).real {a : BoundedSupportRows E (Fin k) |
      (1 / 4 : ℝ) / Real.sqrt k ≤ -minimumValue 1 (boundedFiniteSupport a)} := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  apply (gaussianSupportPrior_gram_event_of_spectral_probability hkd hraw).trans
  apply measureReal_mono _ (measure_ne_top _ _)
  intro a ha
  exact boundedFiniteSupport_negative_of_gram_bound hk a ha

end
end Nonsmooth
