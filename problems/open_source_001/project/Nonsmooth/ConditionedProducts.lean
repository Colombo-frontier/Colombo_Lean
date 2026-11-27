import Nonsmooth.GaussianPriorIdentity

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem finite_product_conditioning {α : Type} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (B : Set α) (hB : MeasurableSet B) (hpos : μ B ≠ 0)
    (k : ℕ) : Measure.pi (fun _ : Fin k => μ[|B]) =
      (Measure.pi (fun _ : Fin k => μ))[|Set.univ.pi (fun _ : Fin k => B)] := by
  letI : IsProbabilityMeasure (μ[|B]) := cond_isProbabilityMeasure hpos
  apply Measure.pi_eq
  intro s hs
  rw [cond_apply (MeasurableSet.univ_pi (fun _ => hB)), Measure.pi_pi]
  have he : (Set.univ.pi (fun _ : Fin k => B)) ∩ Set.univ.pi s =
      Set.univ.pi (fun i => B ∩ s i) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_pi, Set.mem_univ, forall_const]
    constructor
    · intro h i; exact ⟨h.1 i, h.2 i⟩
    · intro h; exact ⟨fun i => (h i).1, fun i => (h i).2⟩
  rw [he, Measure.pi_pi]
  simp_rw [cond_apply hB μ]
  rw [Finset.prod_mul_distrib]
  congr 1
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact ENNReal.inv_pow

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem truncatedGaussianLaw_product_conditioning (k : ℕ) :
    Measure.pi (fun _ : Fin k => truncatedGaussianLaw E) =
      (Measure.pi (fun _ : Fin k => euclideanGaussianLaw E))[|
        Set.univ.pi (fun _ : Fin k => Metric.closedBall (0 : E) (2 * Real.sqrt (Module.finrank ℝ E)))] :=
  finite_product_conditioning (euclideanGaussianLaw E) _ measurableSet_closedBall
    euclideanGaussianLaw_truncation_positive.ne' k

end
end Nonsmooth
