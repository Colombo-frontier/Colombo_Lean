import Nonsmooth.PosteriorCrossMoments

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem orthogonal_integrated_sum_energy {α E : Type} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) [IsProbabilityMeasure μ] {k : ℕ}
    (f : Fin k → α → E) (hf : ∀ i, MemLp (f i) 2 μ)
    (hcross : ∀ i j, i ≠ j → (∫ x, ⟪f i x, f j x⟫_ℝ ∂μ) = 0) :
    (∫ x, ‖∑ i, f i x‖ ^ 2 ∂μ) = ∑ i, ∫ x, ‖f i x‖ ^ 2 ∂μ := by
  have hinner (i j : Fin k) : Integrable (fun x => ⟪f i x, f j x⟫_ℝ) μ :=
    integrable_inner_of_memLp (hf i) (hf j)
  calc
    _ = ∫ x, ∑ i, ∑ j, ⟪f i x, f j x⟫_ℝ ∂μ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      dsimp only
      rw [← real_inner_self_eq_norm_sq, sum_inner]
      simp only [inner_sum]
    _ = ∑ i, ∑ j, ∫ x, ⟪f i x, f j x⟫_ℝ ∂μ := by
      rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hinner i j))]
      apply Finset.sum_congr rfl
      intro i _
      exact integral_finset_sum _ (fun j _ => hinner i j)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · simp only [real_inner_self_eq_norm_sq]
      · intro j _ hji
        exact hcross i j (Ne.symm hji)
      · simp

variable {E H : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [MeasurableSpace H] {k : ℕ}

theorem posteriorCenteredRowMean_memLp (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (X : (Fin k → E) → H) (hX : Measurable X)
    (hLp : ∀ i, MemLp (fun a : Fin k → E => a i) 2 Q) (i : Fin k) :
    MemLp (posteriorCenteredRowMean Q X i) 2 (Q.map X) := by
  let f : (Fin k → E) → E := fun a => a i - ∫ b : Fin k → E, b i ∂Q
  have hf : MemLp f 2 Q := (hLp i).sub (memLp_const _)
  have hfm : StronglyMeasurable f := (measurable_pi_apply i).stronglyMeasurable.sub stronglyMeasurable_const
  have he := condExp_ae_eq_integral_condDistrib_id hX (hf.integrable (by norm_num))
  have hp : MemLp (fun a => posteriorCenteredRowMean Q X i (X a)) 2 Q :=
    (memLp_congr_ae he).mp (hf.condExp (by norm_num))
  have hm : Measurable (posteriorCenteredRowMean Q X i) := hfm.integral_kernel.measurable
  exact (memLp_map_measure_iff hm.aestronglyMeasurable hX.aemeasurable).mpr hp

/-- With independent prior rows and independent actual posterior rows, the
aggregate posterior mean energy is the sum of row mean energies. -/
theorem posterior_centered_sum_energy (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (X : (Fin k → E) → H) (hX : Measurable X)
    (hLp : ∀ i, MemLp (fun a : Fin k → E => a i) 2 Q)
    (hprior : iIndepFun (fun i (a : Fin k → E) => a i) Q)
    (hpost : ∀ᵐ h ∂Q.map X, iIndepFun (fun i (a : Fin k → E) => a i) (condDistrib id X Q h)) :
    (∫ h, ‖∑ i, posteriorCenteredRowMean Q X i h‖ ^ 2 ∂Q.map X) =
      ∑ i, ∫ h, ‖posteriorCenteredRowMean Q X i h‖ ^ 2 ∂Q.map X := by
  letI : IsProbabilityMeasure (Q.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  exact orthogonal_integrated_sum_energy (Q.map X) (posteriorCenteredRowMean Q X)
    (posteriorCenteredRowMean_memLp Q X hX hLp)
    (posterior_centered_cross_zero Q X hX hLp hprior hpost)

end
end Nonsmooth
