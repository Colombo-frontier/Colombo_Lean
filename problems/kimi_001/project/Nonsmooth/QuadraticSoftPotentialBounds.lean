import Nonsmooth.QuadraticSoftNoSpike

open MeasureTheory Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem softplus_upper_abs (t : ℝ) : softplus t ≤ Real.log 2 + |t| := by
  have h0 : 1 ≤ Real.exp |t| := by simpa using Real.exp_le_exp.mpr (abs_nonneg t)
  have ht := Real.exp_le_exp.mpr (le_abs_self t)
  have h := Real.log_le_log (by positivity : 0 < 1 + Real.exp t)
    (show 1 + Real.exp t ≤ 2 * Real.exp |t| by linarith)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp] at h
  exact h

theorem real_quadratic_two_variable_abs_bound (a b c d e f t x : ℝ) :
    |a * t ^ 2 + 2 * b * t * x + c * x ^ 2 + d * t + e * x + f| ≤
      (|a| + |b| + |c| + |d| + |e| + |f|) * (1 + t ^ 2 + x ^ 2) := by
  have h1 := abs_add_le (a * t ^ 2) (2 * b * t * x)
  have h2 := abs_add_le (a * t ^ 2 + 2 * b * t * x) (c * x ^ 2)
  have h3 := abs_add_le (a * t ^ 2 + 2 * b * t * x + c * x ^ 2) (d * t)
  have h4 := abs_add_le (a * t ^ 2 + 2 * b * t * x + c * x ^ 2 + d * t) (e * x)
  have h5 := abs_add_le (a * t ^ 2 + 2 * b * t * x + c * x ^ 2 + d * t + e * x) f
  simp only [abs_mul, abs_pow, sq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h1 h2 h3 h4 h5
  have ht : |t| ≤ 1 + t ^ 2 + x ^ 2 := by nlinarith [sq_nonneg (|t| - 1), sq_abs t, sq_nonneg x]
  have hx : |x| ≤ 1 + t ^ 2 + x ^ 2 := by nlinarith [sq_nonneg (|x| - 1), sq_abs x, sq_nonneg t]
  have htx : 2 * |t| * |x| ≤ 1 + t ^ 2 + x ^ 2 := by
    nlinarith [sq_nonneg (|t| - |x|), sq_abs t, sq_abs x]
  have ha := mul_le_mul_of_nonneg_left (show t ^ 2 ≤ 1 + t ^ 2 + x ^ 2 by nlinarith [sq_nonneg x]) (abs_nonneg a)
  have hb := mul_le_mul_of_nonneg_left htx (abs_nonneg b)
  have hc := mul_le_mul_of_nonneg_left (show x ^ 2 ≤ 1 + t ^ 2 + x ^ 2 by nlinarith [sq_nonneg t]) (abs_nonneg c)
  have hd := mul_le_mul_of_nonneg_left ht (abs_nonneg d)
  have he := mul_le_mul_of_nonneg_left hx (abs_nonneg e)
  have hf := mul_le_mul_of_nonneg_left (show 1 ≤ 1 + t ^ 2 + x ^ 2 by nlinarith [sq_nonneg t, sq_nonneg x]) (abs_nonneg f)
  nlinarith

theorem quadraticSoftSlice_potential_upper {ι : Type} [Fintype ι]
    (ρ : ℝ) (A B C D E F : ι → ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ t x,
      softSlicePotential ρ (quadraticSliceConstraints A B C D E F) t x ≤
        K * (1 + t ^ 2 + x ^ 2) := by
  let L : ι → ℝ := fun i => Real.log 2 + |A i| + |B i| + |C i| + |D i| + |E i| + |F i|
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hL (i : ι) : 0 ≤ L i := by dsimp only [L]; positivity
  let K := 1 + |ρ| + ∑ i, L i
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro t x
  have hi (i : ι) : softplus ((quadraticSliceConstraints A B C D E F).value i t x) ≤
      L i * (1 + t ^ 2 + x ^ 2) := by
    have h := (softplus_upper_abs ((quadraticSliceConstraints A B C D E F).value i t x)).trans
      (add_le_add le_rfl (real_quadratic_two_variable_abs_bound (A i) (B i) (C i) (D i) (E i) (F i) t x))
    apply h.trans
    dsimp only [L]
    nlinarith [mul_nonneg hlog (sq_nonneg t), mul_nonneg hlog (sq_nonneg x)]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  rw [← Finset.sum_mul] at hsum
  have hρ := mul_le_mul_of_nonneg_right (le_abs_self ρ) (add_nonneg (sq_nonneg t) (sq_nonneg x))
  have hsum0 : 0 ≤ ∑ i, L i := Finset.sum_nonneg (fun i _ => hL i)
  dsimp only [softSlicePotential, K]
  nlinarith [mul_nonneg (abs_nonneg ρ) (add_nonneg (sq_nonneg t) (sq_nonneg x)),
    sq_nonneg t, sq_nonneg x, abs_nonneg ρ]

theorem softSlicePotential_quadratic_lower {ι : Type} [Fintype ι]
    (ρ : ℝ) (D : SmoothSliceConstraints ι) (t x : ℝ) :
    ρ / 2 * (t ^ 2 + x ^ 2) ≤ softSlicePotential ρ D t x := by
  have hs : 0 ≤ ∑ i, softplus (D.value i t x) := Finset.sum_nonneg (fun i _ =>
    Real.log_nonneg (by linarith [Real.exp_pos (D.value i t x)]))
  exact le_add_of_nonneg_right hs

end
end Nonsmooth
