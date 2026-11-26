import Nonsmooth.GaussianPolar

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem product_probability_of_slice_bound {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : Set (α × β)) (hs : MeasurableSet s) {c : ℝ} (hc : 0 ≤ c)
    (hb : ∀ x, ν.real (Prod.mk x ⁻¹' s) ≤ c) : (μ.prod ν).real s ≤ c := by
  have h : (μ.prod ν) s ≤ ENNReal.ofReal c := by
    rw [Measure.prod_apply hs]
    calc
      _ ≤ ∫⁻ _x, ENNReal.ofReal c ∂μ := by
        apply lintegral_mono
        intro x
        dsimp only
        rw [← ENNReal.ofReal_toReal (measure_ne_top ν (Prod.mk x ⁻¹' s))]
        exact ENNReal.ofReal_le_ofReal (hb x)
      _ = _ := by simp
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq (ENNReal.toReal_ofReal hc)

end
end Nonsmooth
