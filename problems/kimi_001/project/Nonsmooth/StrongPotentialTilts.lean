import Nonsmooth.StrongPotentialVariance

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem realDensityLaw_integral (w : ℝ → ℝ) (hwm : Measurable w) (hw : Integrable w)
    (hw0 : ∀ x, 0 ≤ w x) (f : ℝ → ℝ) :
    (∫ x, f x ∂realDensityLaw w) = (∫ x, f x * w x) / (∫ x, w x) := by
  rw [realDensityLaw, ProbabilityTheory.cond, Measure.restrict_univ, integral_smul_measure,
    realDensityMeasure_mass w hw hw0, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (integral_nonneg hw0), smul_eq_mul]
  rw [integral_withDensity_eq_integral_toReal_smul hwm.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hw0 _), smul_eq_mul]
  rw [div_eq_inv_mul]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => mul_comm _ _)

theorem strong_potential_tilt_score (U s : ℝ → ℝ) {ρ : ℝ}
    (hd : ∀ x, HasDerivAt U (s x) x) (hmono : Monotone (fun x => s x - ρ * x)) (t : ℝ) :
    (∀ x, HasDerivAt (fun y => U y - t * y) (s x - t) x) ∧
      Monotone (fun x => (s x - t) - ρ * x) := by
  constructor
  · intro x
    convert! (hd x).sub ((hasDerivAt_id x).const_mul t) using 1 <;> simp
  · intro x y hxy
    have h := hmono hxy
    try dsimp only at h ⊢
    linarith

theorem strong_potential_tilt_polynomial_integrable (U s : ℝ → ℝ) (hs : Continuous s)
    {ρ : ℝ} (hρ : 0 < ρ) (hd : ∀ x, HasDerivAt U (s x) x)
    (hmono : Monotone (fun x => s x - ρ * x)) (t : ℝ) (m : ℕ) :
    Integrable (fun x : ℝ => x ^ m * Real.exp (t * x - U x)) := by
  have hU : Continuous U := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have ht := strong_potential_tilt_score U s hd hmono t
  simpa only [neg_sub] using strong_potential_polynomial_integrable
    (fun x => U x - t * x) (fun x => s x - t)
    (hU.sub (continuous_const.mul continuous_id)) (hs.sub continuous_const) hρ ht.1 ht.2 m

theorem strong_potential_tilt_probability_and_memLp (U s : ℝ → ℝ) (hs : Continuous s)
    {ρ : ℝ} (hρ : 0 < ρ) (hd : ∀ x, HasDerivAt U (s x) x)
    (hmono : Monotone (fun x => s x - ρ * x)) (t : ℝ) :
    IsProbabilityMeasure (realDensityLaw (fun x => Real.exp (t * x - U x))) ∧
      MemLp (fun x : ℝ => x) 2 (realDensityLaw (fun x => Real.exp (t * x - U x))) := by
  have ht := strong_potential_tilt_score U s hd hmono t
  simpa only [neg_sub] using strong_potential_law_probability_and_memLp
    (fun x => U x - t * x) (fun x => s x - t) (hs.sub continuous_const) hρ ht.1 ht.2

theorem strong_potential_tilt_law_variance (U s : ℝ → ℝ) (hs : Continuous s)
    {ρ : ℝ} (hρ : 0 < ρ) (hd : ∀ x, HasDerivAt U (s x) x)
    (hmono : Monotone (fun x => s x - ρ * x)) (t : ℝ) :
    variance (fun x : ℝ => x) (realDensityLaw (fun x => Real.exp (t * x - U x))) ≤ ρ⁻¹ := by
  have ht := strong_potential_tilt_score U s hd hmono t
  simpa only [neg_sub] using strong_potential_law_variance
    (fun x => U x - t * x) (fun x => s x - t) (hs.sub continuous_const) hρ ht.1 ht.2

end
end Nonsmooth
