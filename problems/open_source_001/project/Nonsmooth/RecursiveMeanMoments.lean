import Nonsmooth.RecursiveBeliefDisintegration
import Nonsmooth.OrthogonalMeanEnergy

open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {k : ℕ} [Nonempty (Fin k)]

def recursiveSupportMean (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (u : ∀ n, ResponseHistory k n → E) (hu : ∀ n, Measurable (u n))
    (n : ℕ) (h : ResponseHistory k n) : E :=
  ∫ a : Fin k → E, ∑ i, a i ∂recursiveSupportBelief Q u hu n h

theorem recursiveSupportMean_measurable (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (u : ∀ n, ResponseHistory k n → E) (hu : ∀ n, Measurable (u n)) (n : ℕ) :
    Measurable (recursiveSupportMean Q u hu n) := by
  have hf : StronglyMeasurable (fun a : Fin k → E => ∑ i, a i) :=
    (by fun_prop : Continuous (fun a : Fin k → E => ∑ i, a i)).stronglyMeasurable
  exact hf.integral_kernel.measurable

theorem recursiveSupportMean_ae_condExp (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (hi : Integrable (fun a : Fin k → E => ∑ i, a i) Q)
    (u : ∀ n, ResponseHistory k n → E) (hu : ∀ n, Measurable (u n)) (n : ℕ) :
    Q[fun a : Fin k → E => ∑ i, a i |
      MeasurableSpace.comap (recursiveSupportResponse u n) inferInstance] =ᵐ[Q]
      fun a => recursiveSupportMean Q u hu n (recursiveSupportResponse u n a) := by
  have hX := recursiveSupportResponse_measurable u hu n
  have hp := ae_of_ae_map hX.aemeasurable (recursiveSupportBelief_ae_condDistrib Q u hu n)
  filter_upwards [condExp_ae_eq_integral_condDistrib_id hX hi, hp] with a ha hp
  rw [← hp] at ha
  exact ha

theorem recursiveSupportMean_composed_memLp (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (hL : MemLp (fun a : Fin k → E => ∑ i, a i) 2 Q)
    (u : ∀ n, ResponseHistory k n → E) (hu : ∀ n, Measurable (u n)) (n : ℕ) :
    MemLp (fun a => recursiveSupportMean Q u hu n (recursiveSupportResponse u n a)) 2 Q :=
  (memLp_congr_ae (recursiveSupportMean_ae_condExp Q (hL.integrable (by norm_num)) u hu n)).mp
    (hL.condExp (by norm_num))

theorem recursiveSupportMean_memLp (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (hL : MemLp (fun a : Fin k → E => ∑ i, a i) 2 Q)
    (u : ∀ n, ResponseHistory k n → E) (hu : ∀ n, Measurable (u n)) (n : ℕ) :
    MemLp (recursiveSupportMean Q u hu n) 2 (Q.map (recursiveSupportResponse u n)) :=
  (memLp_map_measure_iff (recursiveSupportMean_measurable Q u hu n).aestronglyMeasurable
    (recursiveSupportResponse_measurable u hu n).aemeasurable).mpr
      (recursiveSupportMean_composed_memLp Q hL u hu n)

end
end Nonsmooth
