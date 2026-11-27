import Nonsmooth.ConditionedProducts
import Nonsmooth.GaussianRowTruncation

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem conditional_measureReal {α : Type} [MeasurableSpace α] (μ : Measure α)
    (B : Set α) (hB : MeasurableSet B) (s : Set α) :
    (μ[|B]).real s = μ.real (B ∩ s) / μ.real B := by
  simp only [measureReal_def, cond_apply hB, ENNReal.toReal_mul, ENNReal.toReal_inv]
  ring

theorem conditional_probability_seven_eighths {α : Type} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (B s : Set α) (hB : MeasurableSet B) (hs : MeasurableSet s)
    (hBprob : 15 / 16 ≤ μ.real B) (hsprob : 15 / 16 ≤ μ.real s) :
    7 / 8 ≤ (μ[|B]).real s := by
  rw [conditional_measureReal μ B hB s]
  have hpos : 0 < μ.real B := by linarith
  apply (le_div_iff₀ hpos).mpr
  have hsum := measureReal_union_add_inter (μ := μ) (s := B) hs
  have hu : μ.real (B ∪ s) ≤ 1 := by
    simpa only [measureReal_univ_eq_one] using
      measureReal_mono (μ := μ) (Set.subset_univ (B ∪ s)) (measure_ne_top _ _)
  have hb : μ.real B ≤ 1 := by
    simpa only [measureReal_univ_eq_one] using
      measureReal_mono (μ := μ) (Set.subset_univ B) (measure_ne_top _ _)
  linarith

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem gaussian_truncated_product_event {k : ℕ}
    (hk : (k : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 16)
    (s : Set (Fin k → E)) (hs : MeasurableSet s)
    (hprob : 15 / 16 ≤ (Measure.pi (fun _ : Fin k => euclideanGaussianLaw E)).real s) :
    7 / 8 ≤ (Measure.pi (fun _ : Fin k => truncatedGaussianLaw E)).real s := by
  rw [truncatedGaussianLaw_product_conditioning]
  exact conditional_probability_seven_eighths _ _ s
    (MeasurableSet.univ_pi (fun _ => measurableSet_closedBall)) hs
    (gaussian_rows_truncation_probability hk) hprob

end
end Nonsmooth
