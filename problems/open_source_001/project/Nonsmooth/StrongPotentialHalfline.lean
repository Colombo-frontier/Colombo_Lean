import Nonsmooth.LowerHalflineExhaustion

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem strong_potential_exp_integrable (U s : ℝ → ℝ) (hs : Continuous s)
    {ρ : ℝ} (hρ : 0 < ρ) (hd : ∀ x, HasDerivAt U (s x) x)
    (hmono : Monotone (fun x => s x - ρ * x)) (t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (realDensityLaw (fun x => Real.exp (-U x))) := by
  let m := ∫ y : ℝ, y ∂realDensityLaw (fun y => Real.exp (-U y))
  have he : (fun x : ℝ => Real.exp (t * x)) =
      fun x => Real.exp (t * m) * Real.exp (t * (x - m)) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  exact (strong_potential_centered_exp_integrable U s hs hρ hd hmono t).const_mul _

theorem strong_potential_interval_positive (U s : ℝ → ℝ) (hs : Continuous s)
    {ρ : ℝ} (hρ : 0 < ρ) (hd : ∀ x, HasDerivAt U (s x) x)
    (hmono : Monotone (fun x => s x - ρ * x)) {a b : ℝ} (hab : a < b) :
    realDensityLaw (fun x => Real.exp (-U x)) (Icc a b) ≠ 0 := by
  have hU : Continuous U := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hwc : Continuous (fun x => Real.exp (-U x)) := Real.continuous_exp.comp hU.neg
  have hw : Integrable (fun x => Real.exp (-U x)) := by
    simpa only [pow_zero, one_mul] using strong_potential_polynomial_integrable U s hU hs hρ hd hmono 0
  apply realDensityLaw_interval_positive hab.le _ hwc hw (fun x => (Real.exp_pos _).le)
  exact intervalIntegral.integral_pos hab hwc.continuousOn (fun x _ => (Real.exp_pos _).le)
    ⟨a, ⟨le_rfl, hab.le⟩, Real.exp_pos _⟩

theorem strong_potential_lower_variance (U s : ℝ → ℝ) (hs : Continuous s)
    {ρ : ℝ} (hρ : 0 < ρ) (hd : ∀ x, HasDerivAt U (s x) x)
    (hmono : Monotone (fun x => s x - ρ * x)) (b : ℝ) :
    variance (fun x : ℝ => x) ((realDensityLaw (fun x => Real.exp (-U x)))[|Iic b]) ≤ ρ⁻¹ := by
  have hp := strong_potential_law_probability_and_memLp U s hs hρ hd hmono
  letI := hp.1
  have hU : Continuous U := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hw : Integrable (fun x => Real.exp (-U x)) := by
    simpa only [pow_zero, one_mul] using strong_potential_polynomial_integrable U s hU hs hρ hd hmono 0
  have hwidth (n : ℕ) : b - ((n : ℝ) + 1) < b := by
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  apply lower_halfline_variance_of_intervals _ hp.2 b
    (fun n => strong_potential_interval_positive U s hs hρ hd hmono (hwidth n))
  intro n
  dsimp only [lowerHalflineInterval]
  rw [realDensityLaw_condition_interval _ hw (fun x => (Real.exp_pos _).le)]
  exact convex_potential_interval_law_variance (hwidth n) hρ U s hU hs
    (fun x _ => hd x) (hmono.monotoneOn _)

/-- Sharp centered exponential moments persist after conditioning the actual
strong-potential distribution on a lower half-line. -/
theorem strong_potential_lower_centered_mgf (U s : ℝ → ℝ) (hs : Continuous s)
    {ρ : ℝ} (hρ : 0 < ρ) (hd : ∀ x, HasDerivAt U (s x) x)
    (hmono : Monotone (fun x => s x - ρ * x)) (b t : ℝ) :
    let Q := (realDensityLaw (fun x => Real.exp (-U x)))[|Iic b]
    (∫ x, Real.exp (t * (x - ∫ y : ℝ, y ∂Q)) ∂Q) ≤ Real.exp (t ^ 2 / (2 * ρ)) := by
  have hp := strong_potential_law_probability_and_memLp U s hs hρ hd hmono
  letI := hp.1
  have hU : Continuous U := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hw : Integrable (fun x => Real.exp (-U x)) := by
    simpa only [pow_zero, one_mul] using strong_potential_polynomial_integrable U s hU hs hρ hd hmono 0
  have hwidth (n : ℕ) : b - ((n : ℝ) + 1) < b := by
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  apply lower_halfline_centered_mgf_of_intervals _ (hp.2.integrable (by norm_num)) b t
    (strong_potential_exp_integrable U s hs hρ hd hmono t)
    (fun n => strong_potential_interval_positive U s hs hρ hd hmono (hwidth n))
  intro n
  dsimp only [lowerHalflineInterval]
  simp only [realDensityLaw_condition_interval _ hw (fun x => (Real.exp_pos _).le)]
  exact interval_potential_centered_mgf U s hU hs (hwidth n) hρ
    (fun x _ => hd x) (hmono.monotoneOn _) t

theorem strong_potential_lower_centered_exp_integrable (U s : ℝ → ℝ) (hs : Continuous s)
    {ρ : ℝ} (hρ : 0 < ρ) (hd : ∀ x, HasDerivAt U (s x) x)
    (hmono : Monotone (fun x => s x - ρ * x)) (b t : ℝ) :
    let Q := (realDensityLaw (fun x => Real.exp (-U x)))[|Iic b]
    Integrable (fun x => Real.exp (t * (x - ∫ y : ℝ, y ∂Q))) Q := by
  have hp := strong_potential_law_probability_and_memLp U s hs hρ hd hmono
  letI := hp.1
  have hpos : realDensityLaw (fun x => Real.exp (-U x)) (Iic b) ≠ 0 := by
    intro hz
    exact strong_potential_interval_positive U s hs hρ hd hmono (show b - 1 < b by linarith)
      (measure_mono_null (fun x hx => hx.2) hz)
  let Q := (realDensityLaw (fun x => Real.exp (-U x)))[|Iic b]
  let m := ∫ y : ℝ, y ∂Q
  have he : (fun x => Real.exp (t * (x - m))) = fun x => Real.exp (-t * m) * Real.exp (t * x) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    ring
  change Integrable (fun x => Real.exp (t * (x - m))) Q
  rw [he]
  exact (integrable_under_event (strong_potential_exp_integrable U s hs hρ hd hmono t) hpos).const_mul _

end
end Nonsmooth
