import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! # The actual Gaussian primitive in the zero chain

This is the manuscript's Φ(t)=√e ∫_{-∞}^t exp(-s²/2) ds, expressed with
a Lebesgue set integral. Its derivatives and end-game margin are proved.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace Bilevel.ZeroChainPotential

def kernel (t : ℝ) : ℝ := Real.exp (-t ^ 2 / 2)
def phi (t : ℝ) : ℝ := Real.sqrt (Real.exp 1) * ∫ s in Iic t, kernel s
def phiSlope (t : ℝ) : ℝ := Real.sqrt (Real.exp 1) * kernel t

theorem kernel_integrable : Integrable kernel := by
  have he : kernel = fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
    funext x
    unfold kernel
    congr 1
    ring
  rw [he]
  exact integrable_exp_neg_mul_sq (by norm_num)

theorem kernel_continuous : Continuous kernel := by unfold kernel; fun_prop

theorem phi_eq_interval (t : ℝ) :
    phi t = Real.sqrt (Real.exp 1) * ((∫ s in Iic (0 : ℝ), kernel s) + ∫ s in (0 : ℝ)..t, kernel s) := by
  have h := intervalIntegral.integral_Iic_sub_Iic (μ := volume) (f := kernel) (a := 0) (b := t)
    (kernel_integrable.integrableOn (s := Iic (0 : ℝ)))
    (kernel_integrable.integrableOn (s := Iic t))
  unfold phi
  congr 1
  linarith

theorem phi_hasDerivAt (t : ℝ) : HasDerivAt phi (phiSlope t) t := by
  have hi := intervalIntegral.integral_hasDerivAt_right
    (kernel_integrable.intervalIntegrable (a := 0) (b := t))
    (kernel_continuous.stronglyMeasurableAtFilter volume _) kernel_continuous.continuousAt
  have hd := (hi.const_add (∫ s in Iic (0 : ℝ), kernel s)).const_mul (Real.sqrt (Real.exp 1))
  convert hd using 1
  exact funext phi_eq_interval

theorem phi_deriv (t : ℝ) : deriv phi t = phiSlope t := (phi_hasDerivAt t).deriv

theorem phi_contDiff (n : ℕ) : ContDiff ℝ n phi := by
  cases n with
  | zero => exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr (fun t => (phi_hasDerivAt t).continuousAt))
  | succ n =>
      change ContDiff ℝ ((n : WithTop ℕ∞) + 1) phi
      apply contDiff_succ_iff_deriv.mpr
      refine ⟨fun t => (phi_hasDerivAt t).differentiableAt, ?_, ?_⟩
      · norm_num
      · have he : deriv phi = phiSlope := funext phi_deriv
        rw [he]
        unfold phiSlope kernel
        exact contDiff_const.mul (((contDiff_id.pow 2).neg.div_const 2).exp)

theorem phi_nonneg (t : ℝ) : 0 ≤ phi t := by
  unfold phi
  apply mul_nonneg (by positivity)
  exact integral_nonneg (fun _ => (Real.exp_pos _).le)

theorem phi_bounded (t : ℝ) : phi t ≤ Real.sqrt (Real.exp 1) * Real.sqrt (2 * Real.pi) := by
  have h := setIntegral_le_integral kernel_integrable
    (Filter.Eventually.of_forall (fun x => (Real.exp_pos (-x ^ 2 / 2)).le)) (s := Iic t)
  have he : (∫ s, kernel s) = Real.sqrt (2 * Real.pi) := by
    have hk : kernel = fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
      funext x
      unfold kernel
      congr 1
      ring
    rw [hk, integral_gaussian]
    congr 1
    ring
  rw [he] at h
  exact mul_le_mul_of_nonneg_left h (by positivity)

theorem phi_deriv_nonneg (t : ℝ) : 0 ≤ deriv phi t := by
  rw [phi_deriv]
  unfold phiSlope kernel
  positivity

theorem phi_deriv_ge_one (t : ℝ) (ht : |t| ≤ 1) : 1 ≤ deriv phi t := by
  rw [phi_deriv]
  unfold phiSlope kernel
  rw [← Real.exp_half, ← Real.exp_add]
  apply Real.one_le_exp
  nlinarith [sq_abs t, abs_nonneg t]

theorem phiSlope_hasDerivAt (t : ℝ) : HasDerivAt phiSlope (-t * phiSlope t) t := by
  have hd := ((((hasDerivAt_id t).pow 2).neg.div_const 2).exp).const_mul (Real.sqrt (Real.exp 1))
  convert hd using 1
  unfold phiSlope kernel
  simp only [id_eq]
  ring

theorem phi_second_deriv (t : ℝ) : iteratedDeriv 2 phi t = -t * phiSlope t := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have he : deriv phi = phiSlope := funext phi_deriv
  rw [he, (phiSlope_hasDerivAt t).deriv]

theorem phi_third_deriv (t : ℝ) : iteratedDeriv 3 phi t = (t ^ 2 - 1) * phiSlope t := by
  have h2 : iteratedDeriv 2 phi = fun s => -s * phiSlope s := funext phi_second_deriv
  rw [show 3 = 2 + 1 from rfl, iteratedDeriv_succ, h2]
  have hd := (((hasDerivAt_id t).neg).mul (phiSlope_hasDerivAt t)).deriv
  simp only [id_eq] at hd
  rw [hd]
  ring

theorem kernel_le_one (t : ℝ) : kernel t ≤ 1 := by
  unfold kernel
  apply Real.exp_le_one_iff.mpr
  nlinarith [sq_nonneg t]

theorem quadratic_kernel_bound (t : ℝ) : t ^ 2 * kernel t ≤ 2 := by
  unfold kernel
  rw [show -t ^ 2 / 2 = -(t ^ 2 / 2) by ring, Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  have h := Real.add_one_le_exp (t ^ 2 / 2)
  nlinarith

theorem linear_kernel_bound (t : ℝ) : |t| * kernel t ≤ 3 := by
  have hk : 0 ≤ kernel t := (Real.exp_pos _).le
  have hpol : |t| ≤ 1 + t ^ 2 := by nlinarith [sq_abs t, sq_nonneg (|t| - 1)]
  have h := mul_le_mul_of_nonneg_right hpol hk
  have h0 := kernel_le_one t
  have h2 := quadratic_kernel_bound t
  nlinarith

theorem phi_first_bound (t : ℝ) : |deriv phi t| ≤ Real.sqrt (Real.exp 1) := by
  rw [abs_of_nonneg (phi_deriv_nonneg t), phi_deriv]
  exact (mul_le_mul_of_nonneg_left (kernel_le_one t) (by positivity)).trans_eq (mul_one _)

theorem phi_second_bound (t : ℝ) : |iteratedDeriv 2 phi t| ≤ 3 * Real.sqrt (Real.exp 1) := by
  rw [phi_second_deriv]
  unfold phiSlope
  rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (show 0 ≤ kernel t from (Real.exp_pos _).le)]
  have h := mul_le_mul_of_nonneg_left (linear_kernel_bound t) (Real.sqrt_nonneg (Real.exp 1))
  nlinarith

theorem phi_third_bound (t : ℝ) : |iteratedDeriv 3 phi t| ≤ 3 * Real.sqrt (Real.exp 1) := by
  rw [phi_third_deriv]
  unfold phiSlope
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (show 0 ≤ kernel t from (Real.exp_pos _).le)]
  have hab : |t ^ 2 - 1| ≤ t ^ 2 + 1 := by
    exact (abs_sub (t ^ 2) 1).trans_eq (by simp)
  have hk : 0 ≤ kernel t := (Real.exp_pos _).le
  have h := mul_le_mul_of_nonneg_right hab hk
  have h0 := kernel_le_one t
  have h2 := quadratic_kernel_bound t
  have hs : |t ^ 2 - 1| * kernel t ≤ 3 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg (Real.exp 1))
  nlinarith

theorem phi_uniform_jet_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (j : Fin 4) (t : ℝ), |iteratedDeriv (j : ℕ) phi t| ≤ C := by
  refine ⟨Real.sqrt (Real.exp 1) * Real.sqrt (2 * Real.pi) + 3 * Real.sqrt (Real.exp 1),
    by positivity, ?_⟩
  intro j t
  have hE : 0 ≤ Real.sqrt (Real.exp 1) := Real.sqrt_nonneg _
  have hP : 0 ≤ Real.sqrt (Real.exp 1) * Real.sqrt (2 * Real.pi) := by positivity
  fin_cases j
  · simpa only [Fin.val_zero, iteratedDeriv_zero, abs_of_nonneg (phi_nonneg t)] using
      (phi_bounded t).trans (by linarith)
  · simpa only [Fin.val_one, iteratedDeriv_one] using (phi_first_bound t).trans (by linarith)
  · exact (phi_second_bound t).trans (by linarith)
  · exact (phi_third_bound t).trans (by linarith)

end Bilevel.ZeroChainPotential
