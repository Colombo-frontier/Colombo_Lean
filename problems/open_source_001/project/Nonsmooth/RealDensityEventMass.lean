import Nonsmooth.StrongPotentialTilts

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem realDensityLaw_event_mass (w : ℝ → ℝ) (hw : Integrable w)
    (hw0 : ∀ x, 0 ≤ w x) (A : Set ℝ) (hA : MeasurableSet A) :
    (realDensityLaw w).real A = (∫ x in A, w x) / (∫ x, w x) := by
  have hmass : (volume.withDensity (fun x => ENNReal.ofReal (w x))) A =
      ENNReal.ofReal (∫ x in A, w x) := by
    rw [withDensity_apply _ hA,
      ← ofReal_integral_eq_lintegral_ofReal hw.integrableOn (Eventually.of_forall hw0)]
  rw [measureReal_def, realDensityLaw, cond_apply MeasurableSet.univ, univ_inter,
    realDensityMeasure_mass w hw hw0, hmass, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (integral_nonneg hw0),
    ENNReal.toReal_ofReal (integral_nonneg hw0)]
  exact (div_eq_inv_mul _ _).symm

theorem realDensityLaw_halfline_positive (U : ℝ → ℝ)
    (hi : Integrable (fun x => Real.exp (-U x))) (a : ℝ) :
    0 < (realDensityLaw (fun x => Real.exp (-U x))).real (Iic a) ∧
      0 < (realDensityLaw (fun x => Real.exp (-U x))).real (Ioi a) := by
  have hw0 (x : ℝ) : 0 ≤ Real.exp (-U x) := (Real.exp_pos _).le
  have hZ : 0 < ∫ x, Real.exp (-U x) := integral_exp_pos hi
  have hleft : 0 < ∫ x in Iic a, Real.exp (-U x) := by
    apply integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall hw0) hi.integrableOn |>.mpr
    simp [Function.support, Real.exp_ne_zero]
  have hright : 0 < ∫ x in Ioi a, Real.exp (-U x) := by
    apply integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall hw0) hi.integrableOn |>.mpr
    simp [Function.support, Real.exp_ne_zero]
  rw [realDensityLaw_event_mass _ hi hw0 _ measurableSet_Iic,
    realDensityLaw_event_mass _ hi hw0 _ measurableSet_Ioi]
  exact ⟨div_pos hleft hZ, div_pos hright hZ⟩

end
end Nonsmooth
