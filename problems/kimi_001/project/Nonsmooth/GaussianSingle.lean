import Nonsmooth.GaussianTruncated
import Nonsmooth.SingleSupport

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- The literal source negative-minimum event, proved for its actual Gaussian prior
in the single-row case. This does not assert multi-row or adaptive-output hardness. -/
theorem gaussianSupportPrior_single_negative (hd : 86 ≤ Module.finrank ℝ E) :
    7 / 8 ≤ (gaussianSupportPrior E 1).real
      {a : BoundedSupportRows E (Fin 1) | (1 / 2 : ℝ) / Real.sqrt 1 ≤
        -minimumValue 1 (boundedFiniteSupport a)} := by
  have hp := gaussianSupportPrior_coordinate (E := E) (0 : Fin 1)
  have hs : MeasurableSet {a : Feasible E 2 | 1 / 2 ≤ ‖a.val‖} :=
    (isClosed_le continuous_const continuous_subtype_val.norm).measurableSet
  have he := map_measureReal_apply (μ := gaussianSupportPrior E 1) hp.measurable hs
  rw [hp.map_eq] at he
  have h := gaussianSupportRowLaw_norm_large (E := E) hd
  rw [he] at h
  simpa only [Set.preimage_setOf_eq, boundedFiniteSupport_single_minimum,
    neg_neg, Real.sqrt_one, div_one] using h

end
end Nonsmooth
