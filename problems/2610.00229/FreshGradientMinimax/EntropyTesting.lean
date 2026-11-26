import FreshGradientMinimax.Basic
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-! A quantitative testing obstruction for actual probability measures.
An exponential tilt converts Gibbs' inequality into a lower bound whenever
one measurable event has probability at least 2/3 under P and at most 1/3 under Q. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory InformationTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P Q : Measure Ω}
  [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

theorem entropy_variational_lower {f : Ω → ℝ} (hPQ : P ≪ Q)
    (hi : Integrable (llr P Q) P) (hf : Integrable f P)
    (he : Integrable (fun x => Real.exp (f x)) Q) :
    (∫ x, f x ∂P) - Real.log (∫ x, Real.exp (f x) ∂Q) ≤ ∫ x, llr P Q x ∂P := by
  letI : IsProbabilityMeasure (Q.tilted f) := isProbabilityMeasure_tilted he
  have hc : P ≪ Q.tilted f := hPQ.trans (absolutelyContinuous_tilted he)
  have h := integral_llr_add_sub_measure_univ_nonneg hc
    (integrable_llr_tilted_right hPQ hf hi he)
  rw [integral_llr_tilted_right hPQ hf he hi] at h
  simp only [measureReal_univ_eq_one, add_sub_cancel_right] at h
  linarith

def eventLogWeight (A : Set Ω) : Ω → ℝ := A.indicator (fun _ => Real.log 4)

theorem eventLogWeight_integrable {A : Set Ω} (hA : MeasurableSet A) :
    Integrable (eventLogWeight A) P := (integrable_const _).indicator hA

omit [IsProbabilityMeasure P] in
theorem eventLogWeight_integral {A : Set Ω} (hA : MeasurableSet A) :
    (∫ x, eventLogWeight A x ∂P) = P.real A * Real.log 4 := by
  simp [eventLogWeight, integral_indicator hA, smul_eq_mul]

omit [MeasurableSpace Ω] in
theorem eventLogWeight_exp (A : Set Ω) (x : Ω) :
    Real.exp (eventLogWeight A x) = 1 + A.indicator (fun _ => (3 : ℝ)) x := by
  by_cases hx : x ∈ A
  · norm_num [eventLogWeight, hx, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  · simp [eventLogWeight, hx]

theorem eventLogWeight_exp_integrable {A : Set Ω} (hA : MeasurableSet A) :
    Integrable (fun x => Real.exp (eventLogWeight A x)) P := by
  simp_rw [eventLogWeight_exp]
  exact (integrable_const 1).add ((integrable_const 3).indicator hA)

theorem eventLogWeight_exp_integral {A : Set Ω} (hA : MeasurableSet A) :
    (∫ x, Real.exp (eventLogWeight A x) ∂P) = 1 + 3 * P.real A := by
  simp_rw [eventLogWeight_exp]
  rw [integral_add (integrable_const 1) ((integrable_const 3).indicator hA)]
  simp [integral_indicator hA, smul_eq_mul, mul_comm]

theorem testing_event_information {A : Set Ω} (hA : MeasurableSet A)
    (hPQ : P ≪ Q) (hi : Integrable (llr P Q) P)
    (hP : 2 / 3 ≤ P.real A) (hQ : Q.real A ≤ 1 / 3) :
    Real.log 2 / 3 ≤ ∫ x, llr P Q x ∂P := by
  have h := entropy_variational_lower hPQ hi (eventLogWeight_integrable hA)
    (eventLogWeight_exp_integrable hA)
  rw [eventLogWeight_integral hA, eventLogWeight_exp_integral hA] at h
  have hq0 : 0 ≤ Q.real A := ENNReal.toReal_nonneg
  have hlog : Real.log (1 + 3 * Q.real A) ≤ Real.log 2 :=
    Real.log_le_log (by linarith) (by linarith)
  have hp := mul_le_mul_of_nonneg_right hP (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4))
  have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num, Nat.cast_ofNat] using Real.log_pow (2 : ℝ) 2
  rw [he] at hp h
  linarith

theorem testing_event_kl {A : Set Ω} (hA : MeasurableSet A)
    (hP : 2 / 3 ≤ P.real A) (hQ : Q.real A ≤ 1 / 3) :
    ENNReal.ofReal (Real.log 2 / 3) ≤ klDiv P Q := by
  by_cases hPQ : P ≪ Q
  · by_cases hi : Integrable (llr P Q) P
    · rw [klDiv_of_ac_of_integrable hPQ hi]
      simp only [measureReal_univ_eq_one, add_sub_cancel_right]
      exact ENNReal.ofReal_le_ofReal (testing_event_information hA hPQ hi hP hQ)
    · simp [klDiv_of_not_integrable hi]
  · simp [klDiv_of_not_ac hPQ]

end FreshGradientMinimax
