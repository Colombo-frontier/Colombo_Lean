import Bilevel.GaussianQuadratic

/-! A quadratic exponential certificate for normalized Gaussian directions. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
namespace Bilevel.GaussianDirectionTail
open GaussianQuadratic

def precision (n : ℕ) (t : ℝ) : Fin (n + 1) → ℝ := Fin.cases ((1 + t) / 2) (fun _ => 1 + t / 2)
def tilt (n : ℕ) (t : ℝ) : (Fin (n + 1) → ℝ) → ℝ := quadraticProduct (n + 1) (precision n t)

theorem precision_pos (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (i : Fin (n + 1)) : 0 < precision n t i := by
  induction i using Fin.cases <;> simp only [precision, Fin.cases_zero, Fin.cases_succ] <;> positivity

theorem tilt_integrable (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (tilt n t) (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) :=
  product_integrable (n + 1) (precision n t) (precision_pos n t ht)

theorem tilt_moment (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (∫ x, tilt n t x ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) =
      Real.sqrt (1 / ((1 + t) / 2)) * (Real.sqrt (1 / (1 + t / 2))) ^ n := by
  rw [tilt, product_moment (n + 1) _ (precision_pos n t ht), Fin.prod_univ_succ]
  simp [precision]

theorem sqrt_inverse_le_exp (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.sqrt (1 / (1 + t)) ≤ Real.exp (-t / 4) := by
  have hp : 0 < 1 + t := by linarith
  have he : 1 - (1 + t)⁻¹ = t / (1 + t) := by field_simp
  have hlog := Real.one_sub_inv_le_log_of_pos hp
  rw [he] at hlog
  have hfrac : t / 2 ≤ t / (1 + t) := by
    apply (le_div_iff₀ hp).mpr
    nlinarith [mul_nonneg ht (show 0 ≤ 1 - t by linarith)]
  have h := Real.exp_le_exp.mpr (neg_le_neg (hfrac.trans hlog))
  rw [Real.exp_neg, Real.exp_log hp] at h
  have hs := Real.sqrt_le_sqrt h
  have hexp : Real.exp (-(t / 2)) = Real.exp (-t / 4) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp, Real.sqrt_sq (Real.exp_pos _).le] at hs
  simpa only [one_div] using hs

theorem tilt_moment_bound (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (ht2 : t ≤ 2) :
    (∫ x, tilt n t x ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) ≤
      2 * Real.exp (-(n : ℝ) * t / 8) := by
  rw [tilt_moment n t ht]
  have hp : 0 < (1 + t) / 2 := by positivity
  have hf : Real.sqrt (1 / ((1 + t) / 2)) ≤ 2 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by norm_num, ?_⟩
    apply (div_le_iff₀ hp).mpr
    nlinarith
  have hs : Real.sqrt (1 / (1 + t / 2)) ≤ Real.exp (-t / 8) := by
    simpa only [show -(t / 2) / 4 = -t / 8 by ring] using
      sqrt_inverse_le_exp (t / 2) (by positivity) (by linarith)
  have hpow := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs n
  have hm := mul_le_mul hf hpow (pow_nonneg (Real.sqrt_nonneg _) _) (by norm_num : (0 : ℝ) ≤ 2)
  exact hm.trans_eq (by rw [← Real.exp_nat_mul]; congr 1; congr 1; ring)

theorem tilt_eq_exp (n : ℕ) (t : ℝ) (x : Fin (n + 1) → ℝ) :
    tilt n t x = Real.exp ((1 - t) / 4 * (x 0) ^ 2 - t / 4 * ∑ i : Fin n, (x i.succ) ^ 2) := by
  unfold tilt quadraticProduct
  rw [← Real.exp_sum, Fin.sum_univ_succ]
  simp only [precision, Fin.cases_zero, Fin.cases_succ]
  congr 1
  rw [← Finset.mul_sum]
  ring

theorem tilt_large_on_direction_event (n : ℕ) (t : ℝ) (x : Fin (n + 1) → ℝ)
    (hx : t * (∑ i : Fin (n + 1), (x i) ^ 2) ≤ (x 0) ^ 2) : 1 ≤ tilt n t x := by
  rw [tilt_eq_exp, Real.one_le_exp_iff]
  rw [Fin.sum_univ_succ] at hx
  nlinarith

theorem direction_event_bound (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (ht2 : t ≤ 2) :
    (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)).real
      {x | t * (∑ i : Fin (n + 1), (x i) ^ 2) ≤ (x 0) ^ 2} ≤
        2 * Real.exp (-(n : ℝ) * t / 8) := by
  let μ := Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)
  have hn : 0 ≤ᵐ[μ] tilt n t := Filter.Eventually.of_forall (fun x => by
    rw [tilt_eq_exp]
    exact (Real.exp_pos _).le)
  have hm := mul_meas_ge_le_integral_of_nonneg hn (tilt_integrable n t ht) 1
  simp only [one_mul] at hm
  have hsubset : {x : Fin (n + 1) → ℝ | t * (∑ i : Fin (n + 1), (x i) ^ 2) ≤ (x 0) ^ 2} ⊆
      {x | 1 ≤ tilt n t x} := fun x hx => tilt_large_on_direction_event n t x hx
  have hmono : μ.real {x : Fin (n + 1) → ℝ | t * (∑ i : Fin (n + 1), (x i) ^ 2) ≤ (x 0) ^ 2} ≤
      μ.real {x | 1 ≤ tilt n t x} := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsubset)
  exact hmono.trans (hm.trans (tilt_moment_bound n t ht ht2))

end Bilevel.GaussianDirectionTail
