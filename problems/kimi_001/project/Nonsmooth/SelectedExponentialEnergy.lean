import Nonsmooth.GaussianMaximumMoment

open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

/-- Selecting any one of finitely many candidates costs only the logarithm of
their number. Integrability of the selected nonnegative energy is derived. -/
theorem selected_nonnegative_energy_of_exponential {α : Type} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {k : ℕ} [Nonempty (Fin k)]
    (X : Fin k → α → ℝ) (Z : α → ℝ) (hZ : Measurable Z) (hZ0 : ∀ x, 0 ≤ Z x)
    {t B : ℝ} (ht : 0 < t) (hB : 0 < B)
    (hi : ∀ i, Integrable (fun x => Real.exp (t * X i x)) μ)
    (hb : ∀ i, (∫ x, Real.exp (t * X i x) ∂μ) ≤ B)
    (hsel : ∀ x, ∃ i, Z x ≤ X i x) :
    Integrable Z μ ∧ (∫ x, Z x ∂μ) ≤ Real.log ((k : ℝ) * B) / t := by
  have hp (x : α) : Real.exp (t * Z x) ≤ ∑ i, Real.exp (t * X i x) := by
    obtain ⟨i, h⟩ := hsel x
    exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h ht.le)).trans
      (Finset.single_le_sum (f := fun j => Real.exp (t * X j x))
        (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i))
  have hsum : Integrable (fun x => ∑ i, Real.exp (t * X i x)) μ :=
    integrable_finset_sum _ (fun i _ => hi i)
  have he : Integrable (fun x => Real.exp (t * Z x)) μ := by
    apply hsum.mono' (Real.continuous_exp.measurable.comp (measurable_const.mul hZ)).aestronglyMeasurable
    exact Eventually.of_forall (fun x => by simpa only [Function.comp_apply, Real.norm_of_nonneg (Real.exp_pos _).le, Pi.mul_apply] using hp x)
  have hz : Integrable Z μ := by
    apply (he.div_const t).mono' hZ.aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    rw [Real.norm_of_nonneg (hZ0 x), le_div_iff₀ ht]
    have h := Real.add_one_le_exp (t * Z x)
    nlinarith
  have hK : (0 : ℝ) < k := by
    exact_mod_cast (show 0 < k by simpa only [Fintype.card_fin] using
      (Fintype.card_pos : 0 < Fintype.card (Fin k)))
  refine ⟨hz, integral_le_log_exp_moment μ hz ht (mul_pos hK hB) he ?_⟩
  calc
    _ ≤ ∫ x, ∑ i, Real.exp (t * X i x) ∂μ := integral_mono he hsum hp
    _ = ∑ i, ∫ x, Real.exp (t * X i x) ∂μ := integral_finset_sum _ (fun i _ => hi i)
    _ ≤ ∑ _i : Fin k, B := Finset.sum_le_sum (fun i _ => hb i)
    _ = (k : ℝ) * B := by simp

end
end Nonsmooth
