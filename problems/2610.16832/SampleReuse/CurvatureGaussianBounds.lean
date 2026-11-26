import SampleReuse.CurvaturePotential
import SecondOrder.BoundedC3
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

open scoped BigOperators

namespace SampleReuse
noncomputable section

theorem power_exp_decay_bound (n : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    y^n * Real.exp (-y) ≤ (n.factorial : ℝ) := by
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hp := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp y hy n)
  rw [Real.exp_neg, ← div_eq_mul_inv]
  exact (div_le_iff₀ (Real.exp_pos y)).mpr (by nlinarith only [hp])

theorem gaussian_power_bound (n : ℕ) (x : ℝ) :
    |x^n * Real.exp (-(x^2)/4)| ≤ 1+4^n*(n.factorial : ℝ) := by
  have hbase : |x|^n ≤ 1+(x^2)^n := by
    by_cases hx : |x| ≤ 1
    · have hp := pow_le_pow_left₀ (abs_nonneg x) hx n
      simp only [one_pow] at hp
      exact hp.trans (le_add_of_nonneg_right (pow_nonneg (sq_nonneg x) n))
    · have habs : |x| ≤ x^2 := by nlinarith [sq_abs x, abs_nonneg x, lt_of_not_ge hx]
      exact (pow_le_pow_left₀ (abs_nonneg x) habs n).trans
        (le_add_of_nonneg_left zero_le_one)
  have hdecay := power_exp_decay_bound n (div_nonneg (sq_nonneg x) (by norm_num : (0:ℝ) ≤ 4))
  have hexp : Real.exp (-(x^2)/4) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  have hscale : (x^2)^n = (4:ℝ)^n * (x^2/4)^n := by
    rw [← mul_pow]
    congr 1
    ring
  rw [abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ (1+(x^2)^n)*Real.exp (-(x^2)/4) :=
      mul_le_mul_of_nonneg_right hbase (Real.exp_nonneg _)
    _ = Real.exp (-(x^2)/4)+4^n*((x^2/4)^n*Real.exp (-(x^2)/4)) := by
      rw [hscale]; ring
    _ ≤ 1+4^n*(n.factorial : ℝ) := add_le_add hexp
      (mul_le_mul_of_nonneg_left (by simpa only [neg_div] using hdecay) (by positivity))

def gaussianPolynomialBound (p : Polynomial ℝ) : ℝ :=
  ∑ i ∈ p.support, |p.coeff i| * (1+4^i*(i.factorial : ℝ))

theorem gaussianPolynomialBound_nonneg (p : Polynomial ℝ) :
    0 ≤ gaussianPolynomialBound p := by
  unfold gaussianPolynomialBound
  positivity

theorem polynomial_gaussian_bound (p : Polynomial ℝ) (x : ℝ) :
    |p.eval x * Real.exp (-(x^2)/4)| ≤ gaussianPolynomialBound p := by
  rw [Polynomial.eval_eq_sum]
  change |(∑ i ∈ p.support, p.coeff i*x^i)*Real.exp (-(x^2)/4)| ≤ _
  rw [Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [mul_assoc, abs_mul]
  exact mul_le_mul_of_nonneg_left (gaussian_power_bound i x) (abs_nonneg _)

theorem polynomial_gaussian_hasDerivAt (p : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (fun t => p.eval t * Real.exp (-(t^2)/4))
      ((p.derivative-Polynomial.C (1/2)*Polynomial.X*p).eval x *
        Real.exp (-(x^2)/4)) x := by
  convert (p.hasDerivAt x).mul ((((hasDerivAt_id x).pow 2).neg.div_const 4).exp) using 1
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, id_eq]
  ring

def gaussianDerivativePolynomial : ℕ → Polynomial ℝ
  | 0 => 1
  | n+1 => (gaussianDerivativePolynomial n).derivative -
      Polynomial.C (1/2)*Polynomial.X*gaussianDerivativePolynomial n

theorem gaussian_iteratedDeriv (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => Real.exp (-(x^2)/4)) =
      fun x => (gaussianDerivativePolynomial n).eval x * Real.exp (-(x^2)/4) := by
  induction n with
  | zero => simp [gaussianDerivativePolynomial]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    exact funext (fun x => (polynomial_gaussian_hasDerivAt (gaussianDerivativePolynomial n) x).deriv)

theorem gaussian_boundedC3 : SecondOrder.BoundedC3 (fun x : ℝ => Real.exp (-(x^2)/4)) := by
  let C := ∑ k ∈ Finset.range 4, gaussianPolynomialBound (gaussianDerivativePolynomial k)
  refine ⟨((contDiff_id.pow 2).neg.div_const 4).exp, C,
    Finset.sum_nonneg (fun k _ => gaussianPolynomialBound_nonneg _), ?_⟩
  intro x k hk
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, gaussian_iteratedDeriv]
  exact (polynomial_gaussian_bound _ x).trans
    (Finset.single_le_sum (fun j _ => gaussianPolynomialBound_nonneg _)
      (show k ∈ Finset.range 4 by simpa using Nat.lt_succ_of_le hk))

theorem curvaturePotential_boundedC3 : SecondOrder.BoundedC3 curvaturePotential := by
  simpa only [curvaturePotential, sub_eq_add_neg] using
    (gaussian_boundedC3.add (SecondOrder.boundedC3_const (-1))).const_mul 4

end
end SampleReuse
