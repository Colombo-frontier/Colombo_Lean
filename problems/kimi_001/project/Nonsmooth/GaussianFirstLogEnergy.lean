import Nonsmooth.GaussianFirstMeanFormula

open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section

theorem mean_sum_square_bound {E : Type} [NormedAddCommGroup E] (x y : E) :
    ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := norm_add_le x y
  have h0 := norm_nonneg (x + y)
  nlinarith [norm_nonneg x, norm_nonneg y, sq_nonneg (‖x‖ - ‖y‖)]

theorem first_step_log_arithmetic (m : ℕ) {d : ℝ} (hd : 0 < d) :
    2 * (4 * Real.log (2 * ((m : ℝ) + 3)) / d) + 2 * ((m : ℝ) + 2) ^ 2 *
      ((2 / d) * ((2 * Real.log ((m : ℝ) + 3) + 1) / (((m : ℝ) + 1) * ((m : ℝ) + 2)))) ≤
        32 * Real.log (Real.exp 1 * ((m : ℝ) + 3)) / d := by
  have h1 : 0 < (m : ℝ) + 1 := by positivity
  have h2 : 0 < (m : ℝ) + 2 := by positivity
  have h3 : 0 < (m : ℝ) + 3 := by positivity
  have hratio : ((m : ℝ) + 2) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) ≤ 2 := by
    apply (div_le_iff₀ (mul_pos h1 h2)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hlog : 0 ≤ Real.log ((m : ℝ) + 3) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  calc
    _ = 8 * Real.log (2 * ((m : ℝ) + 3)) / d +
        (4 / d) * (2 * Real.log ((m : ℝ) + 3) + 1) *
          (((m : ℝ) + 2) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2))) := by ring
    _ ≤ 8 * Real.log (2 * ((m : ℝ) + 3)) / d +
        (4 / d) * (2 * Real.log ((m : ℝ) + 3) + 1) * 2 := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hratio (by positivity))
    _ ≤ _ := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) h3.ne',
        Real.log_mul (Real.exp_ne_zero _) h3.ne', Real.log_exp]
      apply (mul_le_mul_iff_of_pos_right hd).mp
      field_simp [hd.ne']
      nlinarith

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem gaussian_first_log_energy_large {u : E} (hu : ‖u‖ = 1) (m : ℕ) :
    (∫ a : Fin (m + 3) → E, ‖((Measure.pi (fun _ : Fin (m + 3) => gaussianAmbientRowLaw E))[
        fun a => ∑ i, a i | MeasurableSpace.comap (supportSingleObservation u) inferInstance]) a‖ ^ 2
      ∂Measure.pi (fun _ : Fin (m + 3) => gaussianAmbientRowLaw E)) ≤
        32 * Real.log (Real.exp 1 * (m + 3 : ℕ)) / (Module.finrank ℝ E : ℝ) := by
  let Q := Measure.pi (fun _ : Fin (m + 3) => gaussianAmbientRowLaw E)
  let M := Q[fun a => ∑ i, a i | MeasurableSpace.comap (supportSingleObservation u) inferInstance]
  have hune : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hu]; norm_num)
  have hM : MemLp M 2 Q := (gaussianAmbientRows_aggregate_memLp (E := E) (k := m + 3)).condExp (by norm_num)
  have hMi := (memLp_two_iff_integrable_sq_norm hM.aestronglyMeasurable).mp hM
  have hY := (gaussianAmbientRows_support_memLp (k := m + 3) hu).integrable_sq
  have hLc : StronglyMeasurable (fun a : Fin (m + 3) → E => gaussianHalfspaceMean u (finiteSupport a u)) :=
    (gaussianHalfspaceMean_stronglyMeasurable u).comp_measurable (supportSingleObservation_measurable u).snd
  have hL : MemLp (fun a : Fin (m + 3) → E => gaussianHalfspaceMean u (finiteSupport a u)) 2 Q :=
    MemLp.of_bound hLc.aestronglyMeasurable 2
      (Eventually.of_forall (fun a => gaussianHalfspaceMean_norm_le u (finiteSupport a u)))
  have hLi := (memLp_two_iff_integrable_sq_norm hL.aestronglyMeasurable).mp hL
  have hR : Integrable (fun a : Fin (m + 3) → E => 2 * (finiteSupport a u) ^ 2 +
      (2 * ((m : ℝ) + 2) ^ 2) * ‖gaussianHalfspaceMean u (finiteSupport a u)‖ ^ 2) Q :=
    (hY.const_mul 2).add (hLi.const_mul (2 * ((m : ℝ) + 2) ^ 2))
  have hbound : (∫ a, ‖M a‖ ^ 2 ∂Q) ≤ ∫ a : Fin (m + 3) → E,
      2 * (finiteSupport a u) ^ 2 +
        (2 * ((m : ℝ) + 2) ^ 2) * ‖gaussianHalfspaceMean u (finiteSupport a u)‖ ^ 2 ∂Q := by
    apply integral_mono_ae hMi hR
    filter_upwards [gaussian_first_condExp_formula (n := m + 2) hu] with a ha
    change ‖M a‖ ^ 2 ≤ _
    change M a = _ at ha
    rw [ha]
    simpa only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hu, one_pow, mul_one,
      Nat.cast_add, Nat.cast_ofNat, mul_assoc] using
      mean_sum_square_bound ((finiteSupport a u) • u)
        (((m + 2 : ℕ) : ℝ) • gaussianHalfspaceMean u (finiteSupport a u))
  rw [integral_add (hY.const_mul 2) (hLi.const_mul _), integral_const_mul, integral_const_mul] at hbound
  have hW := gaussianAmbientRows_support_second_log (k := m + 3) hu
  have hLo := gaussianHalfspaceMean_maximum_energy hune m
  have htotal := hbound.trans (add_le_add
    (mul_le_mul_of_nonneg_left hW (by norm_num : (0 : ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left hLo (by positivity : 0 ≤ 2 * ((m : ℝ) + 2) ^ 2)))
  have hfinal := first_step_log_arithmetic m
    (Nat.cast_pos.mpr Module.finrank_pos : (0 : ℝ) < Module.finrank ℝ E)
  push_cast at htotal ⊢
  exact htotal.trans hfinal

/-- The complete logarithmic first-observation energy estimate for every positive number
of rows and every unit query, under the original actual truncated Gaussian prior. -/
theorem gaussian_first_log_energy_unit {k : ℕ} [Nonempty (Fin k)] {u : E} (hu : ‖u‖ = 1) :
    (∫ a : Fin k → E, ‖((Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E))[
        fun a => ∑ i, a i | MeasurableSpace.comap (supportSingleObservation u) inferInstance]) a‖ ^ 2
      ∂Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)) ≤
        32 * Real.log (Real.exp 1 * k) / (Module.finrank ℝ E : ℝ) := by
  by_cases hk : 3 ≤ k
  · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hk
    have he : k = m + 3 := by omega
    clear hm
    subst k
    exact gaussian_first_log_energy_large hu m
  · have hk2 : (k : ℝ) ≤ 2 := by exact_mod_cast (show k ≤ 2 by omega)
    have hkN : 0 < k := by simpa only [Fintype.card_fin] using
      (Fintype.card_pos : 0 < Fintype.card (Fin k))
    have hk0 : (0 : ℝ) < k := Nat.cast_pos.mpr hkN
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.succ_le_iff.mpr hkN)
    have hlog : 1 ≤ Real.log (Real.exp 1 * k) := by
      rw [Real.log_mul (Real.exp_ne_zero _) hk0.ne', Real.log_exp]
      linarith [Real.log_nonneg hk1]
    apply (gaussian_single_observation_energy (k := k) hu).trans
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    nlinarith

end
end Nonsmooth
