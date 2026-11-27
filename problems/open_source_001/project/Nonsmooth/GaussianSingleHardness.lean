import Nonsmooth.GaussianAdaptiveGap
import Nonsmooth.GaussianSingle

open MeasureTheory ProbabilityTheory Function Filter
open scoped ENNReal InnerProductSpace Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem gaussianSupportPrior_single_output_gap {S : Type} [MeasurableSpace S]
    (p : Policy Unit S (Feasible E 1)) (hp : p.IsMeasurable) (T : ℕ)
    (hd : 86 ≤ Module.finrank ℝ E) (hT : (T : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 128) :
    3 / 4 ≤ (gaussianSupportPrior E 1).real {a : BoundedSupportRows E (Fin 1) |
      7 * ((1 / 2 : ℝ) / Real.sqrt 1) / 16 <
        boundedFiniteSupport a (p.result (fun x => boundedFiniteSupport a x.val) () T).val -
          minimumValue 1 (boundedFiniteSupport a)} := by
  have hs : MeasurableSet {z : E | 7 / 32 < linearPolicyGap p () T z} :=
    measurableSet_lt measurable_const (linearPolicyGap_measurable p hp () T)
  have hrow := gaussianAmbientRowLaw_adaptive_gap p hp () T hd hT
  rw [gaussianAmbientRowLaw, map_measureReal_apply measurable_subtype_coe hs] at hrow
  have hc := gaussianSupportPrior_coordinate (E := E) (0 : Fin 1)
  have hsrow : MeasurableSet {a : Feasible E 2 | 7 / 32 < linearPolicyGap p () T a.val} :=
    measurable_subtype_coe hs
  have hmap := map_measureReal_apply (μ := gaussianSupportPrior E 1) hc.measurable hsrow
  rw [hc.map_eq] at hmap
  simp only [Set.preimage_setOf_eq] at hrow
  rw [hmap] at hrow
  have he (a : BoundedSupportRows E (Fin 1)) :
      linearPolicyGap p () T (a 0).val =
        boundedFiniteSupport a (p.result (fun x => boundedFiniteSupport a x.val) () T).val -
          minimumValue 1 (boundedFiniteSupport a) := by
    simp only [linearPolicyGap, linearPolicyOutput, boundedFiniteSupport_single,
      boundedFiniteSupport_single_minimum, one_mul, sub_neg_eq_add]
  simpa only [Set.preimage_setOf_eq, he, Real.sqrt_one, div_one,
    show 7 * (1 / 2 : ℝ) / 16 = 7 / 32 from by norm_num] using hrow

/-- Every item in the formal external support input is now proved for k=1,
for the actual fixed Gaussian prior, with gamma=1/2, cprob=1/128 and dext=86.
This theorem does not quantify over larger k. -/
theorem gaussianSupportPrior_single_hardness (hd : 86 ≤ Module.finrank ℝ E) :
    (∀ᵐ a ∂gaussianSupportPrior E 1, SupportModel (boundedFiniteSupport a)) ∧
    (7 / 8 ≤ (gaussianSupportPrior E 1).real {a : BoundedSupportRows E (Fin 1) |
      (1 / 2 : ℝ) / Real.sqrt 1 ≤ -minimumValue 1 (boundedFiniteSupport a)}) ∧
    ∀ (T : ℕ), (T : ℝ) ≤ (1 / 128 : ℝ) * Module.finrank ℝ E * 1 / Real.log (Real.exp 1 * 1) →
      ∀ (S : Type) (mS : MeasurableSpace S), letI := mS
        ∀ p : Policy Unit S (Feasible E 1), p.IsMeasurable →
          3 / 4 ≤ (gaussianSupportPrior E 1).real {a : BoundedSupportRows E (Fin 1) |
            7 * ((1 / 2 : ℝ) / Real.sqrt 1) / 16 <
              boundedFiniteSupport a (p.result (fun x => boundedFiniteSupport a x.val) () T).val -
                minimumValue 1 (boundedFiniteSupport a)} := by
  refine ⟨gaussianSupportPrior_model (by norm_num), gaussianSupportPrior_single_negative hd, ?_⟩
  intro T hT S mS p hp
  have hT' : (T : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 128 := by
    simpa only [mul_one, Real.log_exp, div_one, one_div_mul_eq_div] using hT
  exact gaussianSupportPrior_single_output_gap p hp T hd hT'

end
end Nonsmooth
