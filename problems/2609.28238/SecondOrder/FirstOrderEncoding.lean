import SecondOrder.AdaptiveSignConcentration

open MeasureTheory
open scoped BigOperators Classical ENNReal

namespace SecondOrder
noncomputable section

theorem tanh_abs_le_one (x : ℝ) : |Real.tanh x| ≤ 1 := by
  rw [Real.tanh_eq_sinh_div_cosh, abs_div, abs_of_pos (Real.cosh_pos x)]
  apply (div_le_one (Real.cosh_pos x)).mpr
  apply abs_le.mpr
  constructor
  · have h := @Real.sinh_lt_cosh (-x)
    simp only [Real.sinh_neg, Real.cosh_neg] at h
    linarith
  · exact (@Real.sinh_lt_cosh x).le

theorem tanh_continuous : Continuous Real.tanh := by
  rw [show Real.tanh = (fun x => Real.sinh x/Real.cosh x) from
    funext (fun x => Real.tanh_eq_sinh_div_cosh x)]
  exact Real.continuous_sinh.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')

/-- The actual correlation in the first-order hard family, on all query points. -/
def firstOrderEncoding {d : ℕ} (x : Fin d → ℝ) (w : Fin d → Bool) : ℝ :=
  (2/(d:ℝ))*rademacherSum (fun i => Real.tanh (Real.sqrt d*x i)) w

theorem bounded_rademacherSum {d : ℕ} {a : Fin d → ℝ}
    (ha : ∀ i, |a i| ≤ 1) (w : Fin d → Bool) : |rademacherSum a w| ≤ d := by
  calc
    _ ≤ ∑ i, |a i*signValue (w i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      cases hwi : w i <;> simpa [hwi, signValue] using ha i
    _ = _ := by simp

theorem bounded_coefficients_sq_sum {d : ℕ} {a : Fin d → ℝ}
    (ha : ∀ i, |a i| ≤ 1) : ∑ i, a i^2 ≤ d := by
  calc
    _ ≤ ∑ _i : Fin d, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have h := abs_le.mp (ha i)
      nlinarith [sq_nonneg (a i), mul_nonneg (sub_nonneg.mpr h.2) (sub_nonneg.mpr h.1)]
    _ = _ := by simp

theorem firstOrderEncoding_abs_le {d : ℕ} (x : Fin d → ℝ) (w : Fin d → Bool) :
    |firstOrderEncoding x w| ≤ 2 := by
  by_cases hd : d = 0
  · subst d; norm_num [firstOrderEncoding]
  have hd' : (0:ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd)
  rw [firstOrderEncoding, abs_mul, abs_of_pos (div_pos (by norm_num) hd')]
  calc
    _ ≤ (2/(d:ℝ))*d := mul_le_mul_of_nonneg_left
      (bounded_rademacherSum (fun i => tanh_abs_le_one _) w) (by positivity)
    _ = 2 := by field_simp

theorem firstOrderEncoding_joint_measurable {A : Type*} [MeasurableSpace A]
    {d : ℕ} {x : A → Fin d → ℝ} (hx : Measurable x) :
    Measurable (fun w : A × (Fin d → Bool) => firstOrderEncoding (x w.1) w.2) := by
  have ha : Measurable (fun z i => Real.tanh (Real.sqrt d*x z i)) :=
    measurable_pi_lambda _ (fun i => tanh_continuous.measurable.comp
      (((measurable_pi_apply i).comp hx).const_mul _))
  exact (rademacherSum_joint_measurable ha).const_mul _

/-- The first-order activation tail, with the manuscript's explicit constant.
There is no bound on the query point. -/
theorem firstOrderEncoding_tail {d : ℕ} (x : Fin d → ℝ) :
    signLaw d {w | 1/4 < firstOrderEncoding x w} ≤
      ENNReal.ofReal (2*Real.exp (-(d:ℝ)/128)) := by
  by_cases hd : d = 0
  · subst d; norm_num [firstOrderEncoding]
  have hd' : (0:ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd)
  have ht : (0:ℝ) < d/8 := by positivity
  have hb := rademacherSum_hoeffding_proxy
    (fun i => Real.tanh (Real.sqrt d*x i)) hd' ht
    (bounded_coefficients_sq_sum (fun i => tanh_abs_le_one _))
  have he : -(d/8:ℝ)^2/(2*d) = -(d:ℝ)/128 := by field_simp; ring
  rw [he] at hb
  apply (measure_mono (fun w hw => ?_)).trans hb
  change (d:ℝ)/8 ≤ |rademacherSum (fun i => Real.tanh (Real.sqrt d*x i)) w|
  have hh : (d:ℝ)/8 < rademacherSum (fun i => Real.tanh (Real.sqrt d*x i)) w := by
    have hw' : 1/4 < (2/(d:ℝ))*rademacherSum (fun i => Real.tanh (Real.sqrt d*x i)) w := hw
    have := (mul_lt_mul_right hd').mpr hw'
    field_simp at this
    linarith
  exact hh.le.trans (le_abs_self _)

theorem firstOrderEncoding_past_tail {A : Type*} [MeasurableSpace A]
    {η : Measure A} {d : ℕ} {x : A → Fin d → ℝ} (hx : Measurable x)
    {past : Set A} (hp : MeasurableSet past) :
    (η.prod (signLaw d)) {w | w.1 ∈ past ∧ 1/4 < firstOrderEncoding (x w.1) w.2} ≤
      ENNReal.ofReal (2*Real.exp (-(d:ℝ)/128))*η past :=
  fresh_event_past_bound
    (measurableSet_lt measurable_const (firstOrderEncoding_joint_measurable hx))
    (fun z => firstOrderEncoding_tail (x z)) hp

end
end SecondOrder
