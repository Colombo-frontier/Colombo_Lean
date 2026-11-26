import Nonsmooth.StrongPotentialVariance

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

/-- Integration by parts at the fixed origin, retaining the nonnegative
boundary term, controls the raw second moment on an interval containing zero. -/
theorem strong_score_interval_raw_second {a b ρ : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b)
    (w s : ℝ → ℝ) (hw : Continuous w) (hs : Continuous s)
    (hw0 : ∀ x, 0 ≤ w x) (hZ : 0 < ∫ x in a..b, w x)
    (hd : ∀ x ∈ Icc a b, HasDerivAt w (-s x * w x) x)
    (hmono : MonotoneOn (fun x => s x - ρ * x) (Icc a b)) :
    ρ * (∫ x : ℝ, x ^ 2 ∂intervalDensityLaw w a b) ≤
      1 - s 0 * ∫ x : ℝ, x ∂intervalDensityLaw w a b := by
  have hab := ha.trans hb
  have hsw : Continuous (fun x : ℝ => x * s x * w x) := by fun_prop
  have hder (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivAt (fun y : ℝ => y * w y) (w x - x * s x * w x) x := by
    convert! (hasDerivAt_id x).mul (hd x hx) using 1 <;>
      first | rfl | (simp only [id_eq]; ring_nf)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hder x (by simpa only [uIcc_of_le hab] using hx))
    ((hw.sub hsw).intervalIntegrable a b)
  rw [intervalIntegral.integral_sub (hw.intervalIntegrable a b) (hsw.intervalIntegrable a b)] at he
  have hbd : 0 ≤ b * w b - a * w a := by
    nlinarith [mul_nonneg hb (hw0 b), mul_nonpos_of_nonpos_of_nonneg ha (hw0 a)]
  have hp (x : ℝ) (hx : x ∈ Icc a b) :
      ρ * (x ^ 2 * w x) ≤ x * s x * w x - s 0 * (x * w x) := by
    have h := monotone_adjusted_score s hmono hx (show 0 ∈ Icc a b from ⟨ha, hb⟩)
    simp only [sub_zero] at h
    nlinarith [mul_le_mul_of_nonneg_right h (hw0 x)]
  have hcw : Continuous (fun x : ℝ => s 0 * (x * w x)) := by fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab
    ((continuous_const.mul ((continuous_id.pow 2).mul hw)).intervalIntegrable a b)
    ((hsw.sub (continuous_const.mul (continuous_id.mul hw))).intervalIntegrable a b) hp
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, id_eq] at hi
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (hsw.intervalIntegrable a b)
      (hcw.intervalIntegrable a b),
    intervalIntegral.integral_const_mul] at hi
  rw [intervalDensityLaw_integral hab w hw hw0, intervalDensityLaw_integral hab w hw hw0]
  apply (mul_le_mul_iff_of_pos_right hZ).mp
  field_simp
  nlinarith

theorem strong_potential_raw_second_balance (U s : ℝ → ℝ) (hs : Continuous s)
    {ρ : ℝ} (hρ : 0 < ρ) (hd : ∀ x, HasDerivAt U (s x) x)
    (hmono : Monotone (fun x => s x - ρ * x)) :
    ρ * (∫ x : ℝ, x ^ 2 ∂realDensityLaw (fun x => Real.exp (-U x))) ≤
      1 - s 0 * ∫ x : ℝ, x ∂realDensityLaw (fun x => Real.exp (-U x)) := by
  have hU : Continuous U := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hw : Continuous (fun x => Real.exp (-U x)) := Real.continuous_exp.comp hU.neg
  have hwi : Integrable (fun x => Real.exp (-U x)) := by
    simpa only [pow_zero, one_mul] using
      strong_potential_polynomial_integrable U s hU hs hρ hd hmono 0
  have hp := strong_potential_law_probability_and_memLp U s hs hρ hd hmono
  letI := hp.1
  let A : ℕ → Set ℝ := fun n => Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)
  have hA : ∀ n, MeasurableSet (A n) := fun _ => measurableSet_Icc
  have hAm : Monotone A := by
    intro m n hmn x hx
    have hcast : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
    change -((m : ℝ) + 1) ≤ x ∧ x ≤ (m : ℝ) + 1 at hx
    change -((n : ℝ) + 1) ≤ x ∧ x ≤ (n : ℝ) + 1
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hcover : (⋃ n, A n) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    apply mem_iUnion.mpr
    refine ⟨n, ?_⟩
    change -((n : ℝ) + 1) ≤ x ∧ x ≤ (n : ℝ) + 1
    exact ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  have h1 := integral_conditioning_exhaustion_tendsto _ (hp.2.integrable (by norm_num)) A hA hAm hcover
  have h2 := integral_conditioning_exhaustion_tendsto _ hp.2.integrable_sq A hA hAm hcover
  apply le_of_tendsto_of_tendsto (h2.const_mul ρ) (tendsto_const_nhds.sub (h1.const_mul (s 0)))
  apply Eventually.of_forall
  intro n
  dsimp only [A]
  rw [realDensityLaw_condition_interval _ hwi (fun _ => (Real.exp_pos _).le)]
  have hn : 0 ≤ (n : ℝ) + 1 := by positivity
  have hwidth : -((n : ℝ) + 1) < (n : ℝ) + 1 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  apply strong_score_interval_raw_second (by linarith : -((n : ℝ) + 1) ≤ 0) hn
    _ s hw hs (fun _ => (Real.exp_pos _).le)
    (intervalIntegral.integral_pos hwidth hw.continuousOn (fun _ _ => (Real.exp_pos _).le)
      ⟨-((n : ℝ) + 1), ⟨le_rfl, hwidth.le⟩, Real.exp_pos _⟩)
  · intro x _
    convert! (hd x).neg.exp using 1 <;>
      first | rfl | (simp only [Pi.neg_apply]; ring_nf)
  · exact hmono.monotoneOn _

/-- The conditional raw second moment is polynomial in the score at zero,
with no assumed bound on the normalizing constant. -/
theorem strong_potential_raw_second_bound (U s : ℝ → ℝ) (hs : Continuous s)
    {ρ : ℝ} (hρ : 0 < ρ) (hd : ∀ x, HasDerivAt U (s x) x)
    (hmono : Monotone (fun x => s x - ρ * x)) :
    (∫ x : ℝ, x ^ 2 ∂realDensityLaw (fun x => Real.exp (-U x))) ≤
      2 / ρ + (s 0 / ρ) ^ 2 := by
  have hp := strong_potential_law_probability_and_memLp U s hs hρ hd hmono
  letI := hp.1
  have hv := variance_nonneg (fun x : ℝ => x) (realDensityLaw (fun x => Real.exp (-U x)))
  rw [variance_eq_sub hp.2] at hv
  simp only [Pi.pow_apply] at hv
  have hb := strong_potential_raw_second_balance U s hs hρ hd hmono
  have hy := sq_nonneg (ρ * (∫ x : ℝ, x ∂realDensityLaw (fun x => Real.exp (-U x))) + s 0)
  apply (mul_le_mul_iff_of_pos_left (sq_pos_of_pos hρ)).mp
  have hc : ρ ^ 2 * (2 / ρ + (s 0 / ρ) ^ 2) = 2 * ρ + (s 0) ^ 2 := by
    field_simp
    <;> ring
  rw [hc]
  nlinarith [mul_le_mul_of_nonneg_left hb hρ.le,
    mul_nonneg (sq_nonneg ρ) hv]

end
end Nonsmooth
