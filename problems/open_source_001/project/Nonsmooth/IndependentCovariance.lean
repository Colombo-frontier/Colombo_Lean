import Nonsmooth.SupportPosteriorIndependence
import Nonsmooth.GaussianInitialCovariance

open MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {k : ℕ}

theorem independent_rows_directional_variance
    (ν : Measure (Fin k → E)) [IsProbabilityMeasure ν]
    (hI : iIndepFun (fun i (a : Fin k → E) => a i) ν)
    (hLp : ∀ i, MemLp (fun a : Fin k → E => a i) 2 ν) (u : E) :
    variance (fun a : Fin k → E => ⟪u, ∑ i, a i⟫_ℝ) ν =
      ∑ i, variance (fun a : Fin k → E => ⟪u, a i⟫_ℝ) ν := by
  have hi := hI.comp (fun _ (z : E) => ⟪u, z⟫_ℝ)
    (fun _ => (continuous_const.inner continuous_id).measurable)
  have h := IndepFun.variance_sum (s := Finset.univ) (fun i _ => (hLp i).const_inner u)
    (fun i _ j _ hij => hi.indepFun hij)
  simpa only [Finset.sum_fn, inner_sum] using h

theorem independent_rows_centered_second
    (ν : Measure (Fin k → E)) [IsProbabilityMeasure ν]
    (hI : iIndepFun (fun i (a : Fin k → E) => a i) ν)
    (hLp : ∀ i, MemLp (fun a : Fin k → E => a i) 2 ν) (u : E) :
    (∫ a : Fin k → E, ⟪u, (∑ i, a i) - ∫ b : Fin k → E, ∑ i, b i ∂ν⟫_ℝ ^ 2 ∂ν) =
      ∑ i, variance (fun a : Fin k → E => ⟪u, a i⟫_ℝ) ν := by
  have hv : MemLp (fun a : Fin k → E => ∑ i, a i) 2 ν :=
    memLp_finset_sum _ (fun i _ => hLp i)
  have he := independent_rows_directional_variance ν hI hLp u
  rw [variance_eq_integral (hv.const_inner u).aestronglyMeasurable.aemeasurable] at he
  rw [integral_inner (hv.integrable (by norm_num))] at he
  simpa only [inner_sub_right] using he

theorem independent_rows_centered_second_le
    (ν : Measure (Fin k → E)) [IsProbabilityMeasure ν]
    (hI : iIndepFun (fun i (a : Fin k → E) => a i) ν)
    (hLp : ∀ i, MemLp (fun a : Fin k → E => a i) 2 ν)
    (u : E) (v : Fin k → ℝ)
    (hv : ∀ i, variance (fun a : Fin k → E => ⟪u, a i⟫_ℝ) ν ≤ v i) :
    (∫ a : Fin k → E, ⟪u, (∑ i, a i) - ∫ b : Fin k → E, ∑ i, b i ∂ν⟫_ℝ ^ 2 ∂ν) ≤ ∑ i, v i := by
  rw [independent_rows_centered_second ν hI hLp u]
  exact Finset.sum_le_sum (fun i _ => hv i)

end
end Nonsmooth
