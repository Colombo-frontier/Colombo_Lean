import Nonsmooth.GaussianFirstLogEnergy

open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {k : ℕ} [Nonempty (Fin k)]

theorem supportSingleObservation_query_scale (a : Fin k → E) (u : E) {c : ℝ} (hc : 0 < c) :
    supportSingleObservation (c • u) a = (supportWinner a u, c * finiteSupport a u) := by
  have hw : supportWinner a (c • u) = supportWinner a u := by
    apply (supportWinner_eq_iff a (c • u) (supportWinner a u)).mpr
    constructor
    · rw [finiteSupport_homogeneous a hc.le, inner_smul_right, supportWinner_attained a u]
    · intro j hj
      rw [inner_smul_right, finiteSupport_homogeneous a hc.le]
      exact mul_lt_mul_of_pos_left
        (((supportWinner_eq_iff a u (supportWinner a u)).mp rfl).2 j hj) hc
  exact Prod.ext hw (finiteSupport_homogeneous a hc.le u)

theorem supportSingleObservation_information_scale (u : E) {c : ℝ} (hc : 0 < c) :
    MeasurableSpace.comap (supportSingleObservation (k := k) (c • u)) inferInstance =
      MeasurableSpace.comap (supportSingleObservation (k := k) u) inferInstance := by
  let F : Fin k × ℝ → Fin k × ℝ := fun h => (h.1, c * h.2)
  let G : Fin k × ℝ → Fin k × ℝ := fun h => (h.1, c⁻¹ * h.2)
  have hF : Measurable F := measurable_fst.prodMk (measurable_const.mul measurable_snd)
  have hG : Measurable G := measurable_fst.prodMk (measurable_const.mul measurable_snd)
  have he : supportSingleObservation (k := k) (c • u) = F ∘ supportSingleObservation u := by
    funext a
    exact supportSingleObservation_query_scale a u hc
  have hg : supportSingleObservation (k := k) u = G ∘ supportSingleObservation (c • u) := by
    rw [he]
    funext a
    simp only [Function.comp_def, G, F, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  apply le_antisymm
  · rw [he]
    exact measurable_iff_comap_le.mp (hF.comp (Measurable.of_comap_le le_rfl))
  · rw [hg]
    exact measurable_iff_comap_le.mp (hG.comp (Measurable.of_comap_le le_rfl))

theorem supportSingleObservation_information_zero :
    MeasurableSpace.comap (supportSingleObservation (k := k) (0 : E)) inferInstance = ⊥ := by
  have he : supportSingleObservation (k := k) (0 : E) =
      fun _ => (supportWinner (fun _ : Fin k => (0 : E)) 0, (0 : ℝ)) := by
    funext a
    exact Prod.ext (supportWinner_zero a) (finiteSupport_zero a)
  rw [he, MeasurableSpace.comap_const]

variable [Nontrivial E]

theorem gaussian_first_log_energy_arbitrary (q : E) :
    (∫ a : Fin k → E, ‖((Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E))[
        fun a => ∑ i, a i | MeasurableSpace.comap (supportSingleObservation q) inferInstance]) a‖ ^ 2
      ∂Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)) ≤
        32 * Real.log (Real.exp 1 * k) / (Module.finrank ℝ E : ℝ) := by
  by_cases hq : q = 0
  · rw [hq, supportSingleObservation_information_zero, condExp_bot, gaussianAmbientRows_aggregate_mean_zero]
    simp only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), integral_zero]
    have hkN : 0 < k := by simpa only [Fintype.card_fin] using
      (Fintype.card_pos : 0 < Fintype.card (Fin k))
    have hk0 : (0 : ℝ) < k := Nat.cast_pos.mpr hkN
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.succ_le_iff.mpr hkN)
    rw [Real.log_mul (Real.exp_ne_zero _) hk0.ne', Real.log_exp]
    have hlog := Real.log_nonneg hk1
    positivity
  · have hr : ‖q‖ • normalizedDirection q = q := by
      simp [normalizedDirection, smul_smul, norm_ne_zero_iff.mpr hq]
    have hinfo := supportSingleObservation_information_scale (k := k) (normalizedDirection q)
      (norm_pos_iff.mpr hq)
    rw [hr] at hinfo
    rw [hinfo]
    exact gaussian_first_log_energy_unit (normalizedDirection_norm hq)

/-- Complete first-step logarithmic mean increment for the actual augmented transcript,
every policy seed, every positive row count and arbitrary query magnitude. Later adaptive
increments and sharp posterior covariance are not consequences of this initial-step theorem. -/
theorem gaussianSupportMean_first_log_energy {Ω S : Type}
    [MeasurableSpace Ω] [MeasurableSpace S] (p : Policy Ω S E) (ω : Ω) :
    (∫ a : Fin k → E, ‖gaussianSupportMean p ω 1 a - gaussianSupportMean p ω 0 a‖ ^ 2
      ∂Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)) ≤
        32 * Real.log (Real.exp 1 * k) / (Module.finrank ℝ E : ℝ) := by
  rw [gaussianSupportMean_initial]
  simp only [sub_zero]
  simp only [gaussianSupportMean, supportTranscriptInformation_first]
  exact gaussian_first_log_energy_arbitrary (k := k) (p.query 0 ω (p.initial ω))

end
end Nonsmooth
