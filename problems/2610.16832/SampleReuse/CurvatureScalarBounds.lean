import SampleReuse.CurvaturePotential
import SecondOrder.BoundedC3
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Global scalar bounds for the exact gates in the curvature construction.
The constants here are independent of the eventual chain length. -/

open scoped BigOperators

namespace SampleReuse
noncomputable section

theorem inv_power_glue_bound (n : ℕ) (t : ℝ) :
    |t⁻¹^n * expNegInvGlue t| ≤ (n.factorial : ℝ) := by
  by_cases ht : t ≤ 0
  · simp [expNegInvGlue.zero_of_nonpos ht]
  have hp : 0 < t := lt_of_not_ge ht
  have he := Real.pow_div_factorial_le_exp t⁻¹ (inv_nonneg.mpr hp.le) n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hpow : t⁻¹^n ≤ (n.factorial : ℝ) * Real.exp t⁻¹ :=
    by nlinarith [(div_le_iff₀ hf).mp he]
  rw [abs_of_nonneg (mul_nonneg (pow_nonneg (inv_nonneg.mpr hp.le) n)
    (expNegInvGlue.nonneg t)), expNegInvGlue, if_neg ht, Real.exp_neg]
  rw [← div_eq_mul_inv]
  exact (div_le_iff₀ (Real.exp_pos t⁻¹)).mpr hpow

def gluePolynomialBound (p : Polynomial ℝ) : ℝ :=
  ∑ i ∈ p.support, |p.coeff i| * (i.factorial : ℝ)

theorem gluePolynomialBound_nonneg (p : Polynomial ℝ) : 0 ≤ gluePolynomialBound p := by
  unfold gluePolynomialBound
  positivity

theorem polynomial_glue_bound (p : Polynomial ℝ) (t : ℝ) :
    |p.eval t⁻¹ * expNegInvGlue t| ≤ gluePolynomialBound p := by
  rw [Polynomial.eval_eq_sum]
  change |(∑ i ∈ p.support, p.coeff i * t⁻¹^i) * expNegInvGlue t| ≤ _
  rw [Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [mul_assoc, abs_mul]
  exact mul_le_mul_of_nonneg_left (inv_power_glue_bound i t) (abs_nonneg _)

def glueDerivativePolynomial : ℕ → Polynomial ℝ
  | 0 => 1
  | n+1 => Polynomial.X^2 *
      (glueDerivativePolynomial n - (glueDerivativePolynomial n).derivative)

theorem glue_iteratedDeriv (n : ℕ) :
    iteratedDeriv n expNegInvGlue =
      fun t => (glueDerivativePolynomial n).eval t⁻¹ * expNegInvGlue t := by
  induction n with
  | zero => simp [glueDerivativePolynomial]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    exact funext (fun t =>
      (expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (glueDerivativePolynomial n) t).deriv)

theorem glue_boundedC3 : SecondOrder.BoundedC3 expNegInvGlue := by
  let C := ∑ k ∈ Finset.range 4, gluePolynomialBound (glueDerivativePolynomial k)
  refine ⟨expNegInvGlue.contDiff, C,
    Finset.sum_nonneg (fun k _ => gluePolynomialBound_nonneg _), ?_⟩
  intro x k hk
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, glue_iteratedDeriv]
  exact (polynomial_glue_bound _ x).trans
    (Finset.single_le_sum (fun j _ => gluePolynomialBound_nonneg _)
      (show k ∈ Finset.range 4 by simpa using Nat.lt_succ_of_le hk))

theorem boundedC3_shift {f : ℝ → ℝ} (hf : SecondOrder.BoundedC3 f) (s : ℝ) :
    SecondOrder.BoundedC3 (fun x => f (x+s)) := by
  obtain ⟨hf, C, hC, hb⟩ := hf
  refine ⟨hf.comp (contDiff_id.add contDiff_const), C, hC, ?_⟩
  intro x k hk
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_comp_add_const,
    ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact hb (x+s) k hk

theorem boundedC3_reflect {f : ℝ → ℝ} (hf : SecondOrder.BoundedC3 f) :
    SecondOrder.BoundedC3 (fun x => f (-x)) := by
  obtain ⟨hf, C, hC, hb⟩ := hf
  refine ⟨hf.comp contDiff_id.neg, C, hC, ?_⟩
  intro x k hk
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_comp_neg, norm_smul]
  simp only [norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact hb (-x) k hk

theorem curvatureGate_boundedC3 : SecondOrder.BoundedC3 curvatureGate := by
  simpa only [curvatureGate, sub_eq_add_neg, neg_div] using
    (boundedC3_shift glue_boundedC3 (-(1:ℝ)/2)).add
      (boundedC3_reflect (boundedC3_shift glue_boundedC3 (-(1:ℝ)/2)))

end
end SampleReuse
