import SecondOrder.RademacherMoments
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

open MeasureTheory Filter
open scoped BigOperators Classical ENNReal

namespace SecondOrder
noncomputable section

theorem sign_exp_mean (x : ℝ) :
    uniformMean (fun b : Bool => Real.exp (x*signValue b)) = Real.cosh x := by
  rw [uniformMean_bool, Real.cosh_eq]
  simp [signValue, add_comm]

theorem rademacherSum_exp_mean {d : ℕ} (a : Fin d → ℝ) (ℓ : ℝ) :
    uniformMean (fun w => Real.exp (ℓ*rademacherSum a w)) = ∏ i, Real.cosh (ℓ*a i) := by
  induction d with
  | zero => simp [rademacherSum]
  | succ d ih =>
    rw [uniformMean_snoc d]
    simp_rw [rademacherSum_snoc, mul_add, Real.exp_add,
      show ∀ b : Bool, ℓ*(a (Fin.last d)*signValue b) = (ℓ*a (Fin.last d))*signValue b by
        intro b; ring,
      uniformMean_mul, sign_exp_mean]
    have he : (fun w => Real.exp (ℓ*rademacherSum (fun i => a i.castSucc) w)*
        Real.cosh (ℓ*a (Fin.last d))) =
        fun w => Real.cosh (ℓ*a (Fin.last d))*Real.exp (ℓ*rademacherSum (fun i => a i.castSucc) w) := by
      funext w; ring
    rw [he, uniformMean_mul, ih, Fin.prod_univ_castSucc]
    ring

theorem rademacherSum_exp_bound {d : ℕ} (a : Fin d → ℝ) (ℓ : ℝ) :
    uniformMean (fun w => Real.exp (ℓ*rademacherSum a w)) ≤
      Real.exp (ℓ^2*(∑ i, a i^2)/2) := by
  rw [rademacherSum_exp_mean]
  calc
    _ ≤ ∏ i, Real.exp ((ℓ*a i)^2/2) :=
      Finset.prod_le_prod (fun i _ => (Real.cosh_pos _).le) (fun i _ => Real.cosh_le_exp_half_sq _)
    _ = Real.exp (∑ i, (ℓ*a i)^2/2) := (Real.exp_sum _ _).symm
    _ = _ := by
      congr 1
      calc
        _ = ∑ i, (ℓ^2/2)*a i^2 := Finset.sum_congr rfl (fun _ _ => by ring)
        _ = (ℓ^2/2)*(∑ i, a i^2) := (Finset.mul_sum _ _ _).symm
        _ = _ := by ring

/-- Exponential Markov on the actual finite sign law. -/
theorem signLaw_exp_tail {d : ℕ} (X : (Fin d → Bool) → ℝ)
    {ℓ t : ℝ} (hℓ : 0 ≤ ℓ) :
    signLaw d {w | t ≤ X w} ≤ ENNReal.ofReal
      (Real.exp (-ℓ*t)*uniformMean (fun w => Real.exp (ℓ*X w))) := by
  have hi : Integrable (fun w => Real.exp (ℓ*X w)/Real.exp (ℓ*t)) (signLaw d) := Integrable.of_finite
  have hp := hi.measure_le_integral
    (Eventually.of_forall (fun w => div_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))
    (s := {w | t ≤ X w}) (fun w hw => by
      apply (le_div_iff₀ (Real.exp_pos _)).mpr
      simpa using Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hw hℓ))
  apply hp.trans_eq
  congr 1
  rw [integral_div, integral_signLaw, div_eq_mul_inv, ← Real.exp_neg]
  rw [neg_mul]
  ring

/-- A variance proxy lets the same inequality apply after conditioning
on a matching, where only an upper bound for the squared coefficients is known. -/
theorem rademacherSum_upper_tail {d : ℕ} (a : Fin d → ℝ) {v t : ℝ}
    (hv : 0 < v) (ht : 0 < t) (ha : ∑ i, a i^2 ≤ v) :
    signLaw d {w | t ≤ rademacherSum a w} ≤ ENNReal.ofReal (Real.exp (-t^2/(2*v))) := by
  apply (signLaw_exp_tail (rademacherSum a) (ℓ := t/v) (div_nonneg ht.le hv.le)).trans
  apply ENNReal.ofReal_le_ofReal
  have hm := (rademacherSum_exp_bound a (t/v)).trans
    (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left ha (sq_nonneg _)) (by norm_num : (0:ℝ) ≤ 2)))
  calc
    _ ≤ Real.exp (-(t/v)*t)*Real.exp ((t/v)^2*v/2) :=
      mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; field_simp; ring

theorem rademacherSum_hoeffding_proxy {d : ℕ} (a : Fin d → ℝ) {v t : ℝ}
    (hv : 0 < v) (ht : 0 < t) (ha : ∑ i, a i^2 ≤ v) :
    signLaw d {w | t ≤ |rademacherSum a w|} ≤ ENNReal.ofReal (2*Real.exp (-t^2/(2*v))) := by
  have hn : ∀ w, rademacherSum (fun i => -a i) w = -rademacherSum a w := by
    intro w
    simp [rademacherSum, neg_mul, Finset.sum_neg_distrib]
  have he : {w | t ≤ |rademacherSum a w|} =
      {w | t ≤ rademacherSum a w} ∪ {w | t ≤ rademacherSum (fun i => -a i) w} := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_union, hn, le_abs]
  rw [he]
  have hb := measure_union_le (μ := signLaw d)
    {w | t ≤ rademacherSum a w} {w | t ≤ rademacherSum (fun i => -a i) w}
  apply hb.trans
  have hneg := rademacherSum_upper_tail (fun i => -a i) hv ht (by simpa using ha)
  have hh := add_le_add (rademacherSum_upper_tail a hv ht ha) hneg
  exact hh.trans_eq (by rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]; congr 1; ring)

/-- The manuscript's Rademacher Hoeffding inequality, including the
degenerate zero-coefficient case (whose tail probability is zero). -/
theorem rademacherSum_hoeffding {d : ℕ} (a : Fin d → ℝ) {t : ℝ} (ht : 0 < t) :
    signLaw d {w | t ≤ |rademacherSum a w|} ≤
      ENNReal.ofReal (2*Real.exp (-t^2/(2*(∑ i, a i^2)))) := by
  have hv : 0 ≤ ∑ i, a i^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rcases hv.eq_or_lt with hz | hp
  · have ha (i : Fin d) : a i = 0 := by
      have hi := Finset.single_le_sum (fun j _ => sq_nonneg (a j)) (Finset.mem_univ i)
      rw [← hz] at hi
      nlinarith [sq_nonneg (a i)]
    simp only [rademacherSum, ha, zero_mul, Finset.sum_const_zero, abs_zero,
      not_le.mpr ht, Set.setOf_false, measure_empty, zero_le]
  · exact rademacherSum_hoeffding_proxy a hp ht le_rfl

end
end SecondOrder
