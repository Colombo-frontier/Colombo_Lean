import Nonsmooth.OrthogonalMeanEnergy

open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E H : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [MeasurableSpace H] {k : ℕ}

def posteriorAggregateShift (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (X : (Fin k → E) → H) (h : H) : E :=
  (∫ a : Fin k → E, ∑ i, a i ∂condDistrib id X Q h) - ∫ a : Fin k → E, ∑ i, a i ∂Q

theorem posteriorAggregateShift_eq_sum (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (X : (Fin k → E) → H)
    (hLp : ∀ i, MemLp (fun a : Fin k → E => a i) 2 Q) :
    ∀ᵐ h ∂Q.map X, posteriorAggregateShift Q X h = ∑ i, posteriorCenteredRowMean Q X i h := by
  filter_upwards [posterior_rows_memLp_two Q X hLp] with h hh
  have hrow (i : Fin k) : posteriorCenteredRowMean Q X i h =
      (∫ a : Fin k → E, a i ∂condDistrib id X Q h) - ∫ a : Fin k → E, a i ∂Q := by
    rw [posteriorCenteredRowMean, integral_sub ((hh i).integrable (by norm_num)) (integrable_const _),
      integral_const, measureReal_univ_eq_one, one_smul]
  simp_rw [hrow]
  rw [posteriorAggregateShift,
    integral_finset_sum _ (fun i _ => (hh i).integrable (by norm_num)),
    integral_finset_sum _ (fun i _ => (hLp i).integrable (by norm_num)),
    Finset.sum_sub_distrib]

theorem posteriorAggregateShift_memLp (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (X : (Fin k → E) → H) (hX : Measurable X)
    (hLp : ∀ i, MemLp (fun a : Fin k → E => a i) 2 Q) :
    MemLp (posteriorAggregateShift Q X) 2 (Q.map X) := by
  have hs : MemLp (fun h => ∑ i, posteriorCenteredRowMean Q X i h) 2 (Q.map X) :=
    memLp_finset_sum _ (fun i _ => posteriorCenteredRowMean_memLp Q X hX hLp i)
  exact (memLp_congr_ae (posteriorAggregateShift_eq_sum Q X hLp)).mpr hs

/-- Exact aggregate mean energy decomposition for an actual posterior that
retains independence of the prior rows. -/
theorem posterior_aggregate_energy_eq_row_sum (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (X : (Fin k → E) → H) (hX : Measurable X)
    (hLp : ∀ i, MemLp (fun a : Fin k → E => a i) 2 Q)
    (hprior : iIndepFun (fun i (a : Fin k → E) => a i) Q)
    (hpost : ∀ᵐ h ∂Q.map X, iIndepFun (fun i (a : Fin k → E) => a i) (condDistrib id X Q h)) :
    (∫ h, ‖posteriorAggregateShift Q X h‖ ^ 2 ∂Q.map X) =
      ∑ i, ∫ h, ‖posteriorCenteredRowMean Q X i h‖ ^ 2 ∂Q.map X := by
  calc
    _ = ∫ h, ‖∑ i, posteriorCenteredRowMean Q X i h‖ ^ 2 ∂Q.map X := by
      apply integral_congr_ae
      filter_upwards [posteriorAggregateShift_eq_sum Q X hLp] with h hh
      rw [hh]
    _ = _ := posterior_centered_sum_energy Q X hX hLp hprior hpost

end
end Nonsmooth
