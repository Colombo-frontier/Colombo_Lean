import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic

/-!
# Chebyshev approximation of the inverse

This module proves `zv:lem:polynomial` from 0113.tex. For `0 < μ < M`,
the explicit polynomial `inverseApprox μ M m` has degree at most `m - 1`
and satisfies both advertised uniform bounds on `[μ,M]`. The denominator
identity and Chebyshev interval bounds are proved using Mathlib's actual
polynomials and real trigonometric/hyperbolic functions.
-/

noncomputable section
open Polynomial

namespace Bilevel.InversePolynomial

def rate (μ M : ℝ) : ℝ := (Real.sqrt (M / μ) - 1) / (Real.sqrt (M / μ) + 1)

theorem rate_range {μ M : ℝ} (hμ : 0 < μ) (hM : μ < M) :
    0 < rate μ M ∧ rate μ M < 1 := by
  have hk : 1 < M / μ := (lt_div_iff₀ hμ).mpr (by simpa using hM)
  have hs : 1 < Real.sqrt (M / μ) := (Real.lt_sqrt (by norm_num)).mpr (by simpa using hk)
  constructor
  · exact div_pos (sub_pos.mpr hs) (by linarith)
  · apply (div_lt_one (by linarith : 0 < Real.sqrt (M / μ) + 1)).mpr
    linarith

theorem midpoint_identity {μ M : ℝ} (hμ : 0 < μ) (hM : μ < M) :
    (M + μ) / (M - μ) = (rate μ M + (rate μ M)⁻¹) / 2 := by
  have hk : 0 ≤ M / μ := le_of_lt (div_pos (lt_trans hμ hM) hμ)
  let s := Real.sqrt (M / μ)
  have hs : s ^ 2 * μ = M := by
    rw [show s ^ 2 = M / μ from Real.sq_sqrt hk, div_mul_cancel₀ _ hμ.ne']
  have hroot : 1 < s := by
    apply (Real.lt_sqrt (by norm_num)).mpr
    have hh : 1 < M / μ := (lt_div_iff₀ hμ).mpr (by simpa using hM)
    simpa using hh
  change (M + μ) / (M - μ) = ((s - 1) / (s + 1) + ((s - 1) / (s + 1))⁻¹) / 2
  have hsp : s + 1 ≠ 0 := by linarith
  have hsm : s - 1 ≠ 0 := by linarith
  field_simp [hsp, hsm, sub_ne_zero.mpr hM.ne']
  nlinarith

theorem chebyshev_degree (m : ℕ) : (Polynomial.Chebyshev.T ℝ (m : ℤ)).natDegree ≤ m := by
  induction m using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih0 ih1 =>
    rw [Nat.cast_add, Nat.cast_ofNat, Polynomial.Chebyshev.T_add_two]
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · have htwo : ((2 : ℝ[X]) * X).natDegree ≤ 1 := by
        simp
      have hmul := Polynomial.natDegree_mul_le (p := (2 : ℝ[X]) * X)
        (q := Polynomial.Chebyshev.T ℝ ((n : ℤ) + 1))
      have hi : (Polynomial.Chebyshev.T ℝ ((n : ℤ) + 1)).natDegree ≤ n + 1 := by
        simpa using ih1
      omega
    · omega

theorem chebyshev_interval {x : ℝ} (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (m : ℕ) :
    |(Polynomial.Chebyshev.T ℝ (m : ℤ)).eval x| ≤ 1 := by
  rw [← Real.cos_arccos hx0 hx1, Polynomial.Chebyshev.T_real_cos]
  exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

theorem chebyshev_outside {q : ℝ} (hq : 0 < q) (m : ℕ) :
    (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval ((q + q⁻¹) / 2) =
      (q ^ m + (q ^ m)⁻¹) / 2 := by
  rw [← Real.cosh_log hq, Polynomial.Chebyshev.T_real_cosh]
  simp only [Int.cast_natCast, Real.cosh_eq, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hq]

def affine (μ M : ℝ) : ℝ[X] := C ((M + μ) / (M - μ)) - C (2 / (M - μ)) * X

def denominator (μ M : ℝ) (m : ℕ) : ℝ :=
  (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval ((M + μ) / (M - μ))

def residual (μ M : ℝ) (m : ℕ) : ℝ[X] :=
  C (denominator μ M m)⁻¹ * (Polynomial.Chebyshev.T ℝ (m : ℤ)).comp (affine μ M)

def inverseApprox (μ M : ℝ) (m : ℕ) : ℝ[X] := (1 - residual μ M m).divX

theorem denominator_formula {μ M : ℝ} (hμ : 0 < μ) (hM : μ < M) (m : ℕ) :
    denominator μ M m = ((rate μ M) ^ m + ((rate μ M) ^ m)⁻¹) / 2 := by
  unfold denominator
  rw [midpoint_identity hμ hM]
  exact chebyshev_outside (rate_range hμ hM).1 m

theorem denominator_pos {μ M : ℝ} (hμ : 0 < μ) (hM : μ < M) (m : ℕ) :
    0 < denominator μ M m := by
  rw [denominator_formula hμ hM]
  have hq := (rate_range hμ hM).1
  positivity

theorem affine_degree (μ M : ℝ) : (affine μ M).natDegree ≤ 1 := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · simp
  · simpa using (Polynomial.natDegree_mul_le (p := C (2 / (M - μ))) (q := X))

theorem residual_degree (μ M : ℝ) (m : ℕ) : (residual μ M m).natDegree ≤ m := by
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  calc
    _ ≤ (Polynomial.Chebyshev.T ℝ (m : ℤ)).natDegree * (affine μ M).natDegree :=
      Polynomial.natDegree_comp_le
    _ ≤ m * 1 := Nat.mul_le_mul (chebyshev_degree m) (affine_degree μ M)
    _ = m := Nat.mul_one m

theorem inverseApprox_degree (μ M : ℝ) (m : ℕ) :
    (inverseApprox μ M m).natDegree ≤ m - 1 := by
  rw [inverseApprox, Polynomial.natDegree_divX_eq_natDegree_tsub_one]
  apply Nat.sub_le_sub_right
  exact (Polynomial.natDegree_sub_le _ _).trans (by simpa using residual_degree μ M m)

theorem residual_zero {μ M : ℝ} (hμ : 0 < μ) (hM : μ < M) (m : ℕ) :
    (residual μ M m).eval 0 = 1 := by
  simp only [residual, eval_mul, eval_C, eval_comp, affine, eval_sub, eval_X,
    mul_zero, sub_zero]
  exact inv_mul_cancel₀ (denominator_pos hμ hM m).ne'

theorem inverseApprox_identity {μ M : ℝ} (hμ : 0 < μ) (hM : μ < M) (m : ℕ) (x : ℝ) :
    (inverseApprox μ M m).eval x * x = 1 - (residual μ M m).eval x := by
  have hzero : (1 - residual μ M m).coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, eval_sub, eval_one, residual_zero hμ hM]
    simp
  have hid := Polynomial.divX_mul_X_add (1 - residual μ M m)
  rw [hzero, C_0, add_zero] at hid
  have hv := congrArg (Polynomial.eval x) hid
  simpa only [eval_mul, eval_X, eval_sub, eval_one, inverseApprox] using hv

theorem affine_eval (μ M x : ℝ) :
    (affine μ M).eval x = (M + μ - 2 * x) / (M - μ) := by
  simp only [affine, eval_sub, eval_C, eval_mul, eval_X]
  ring

theorem affine_interval {μ M x : ℝ} (hM : μ < M) (hx0 : μ ≤ x) (hx1 : x ≤ M) :
    -1 ≤ (affine μ M).eval x ∧ (affine μ M).eval x ≤ 1 := by
  rw [affine_eval]
  constructor
  · apply (le_div_iff₀ (sub_pos.mpr hM)).mpr
    linarith
  · apply (div_le_iff₀ (sub_pos.mpr hM)).mpr
    linarith

theorem inverse_denominator_bound {μ M : ℝ} (hμ : 0 < μ) (hM : μ < M) (m : ℕ) :
    1 / denominator μ M m ≤ 2 * (rate μ M) ^ m := by
  apply (div_le_iff₀ (denominator_pos hμ hM m)).mpr
  have hpow : (rate μ M) ^ m ≠ 0 := (pow_pos (rate_range hμ hM).1 _).ne'
  have hid : 2 * (rate μ M) ^ m * denominator μ M m = ((rate μ M) ^ m) ^ 2 + 1 := by
    rw [denominator_formula hμ hM]
    field_simp
    ring
  nlinarith [sq_nonneg ((rate μ M) ^ m)]

theorem residual_bound {μ M x : ℝ} (hμ : 0 < μ) (hM : μ < M)
    (hx0 : μ ≤ x) (hx1 : x ≤ M) (m : ℕ) :
    |(residual μ M m).eval x| ≤ 2 * (rate μ M) ^ m := by
  have hden := denominator_pos hμ hM m
  have hx := affine_interval hM hx0 hx1
  have hc := chebyshev_interval hx.1 hx.2 m
  simp only [residual, eval_mul, eval_C, eval_comp, abs_mul, abs_inv, abs_of_pos hden]
  calc
    _ ≤ (denominator μ M m)⁻¹ * 1 := mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr hden.le)
    _ = 1 / denominator μ M m := by ring
    _ ≤ _ := inverse_denominator_bound hμ hM m

theorem inverseApprox_error {μ M x : ℝ} (hμ : 0 < μ) (hM : μ < M)
    (hx0 : μ ≤ x) (hx1 : x ≤ M) (m : ℕ) :
    |(inverseApprox μ M m).eval x - 1 / x| ≤ (2 / μ) * (rate μ M) ^ m := by
  have hx : 0 < x := lt_of_lt_of_le hμ hx0
  have hid := inverseApprox_identity hμ hM m x
  have herr : (inverseApprox μ M m).eval x - 1 / x = -(residual μ M m).eval x / x := by
    apply (eq_div_iff hx.ne').mpr
    field_simp
    nlinarith
  rw [herr, abs_div, abs_neg, abs_of_pos hx]
  calc
    _ ≤ (2 * (rate μ M) ^ m) / x := div_le_div_of_nonneg_right
      (residual_bound hμ hM hx0 hx1 m) hx.le
    _ ≤ (2 * (rate μ M) ^ m) / μ := div_le_div_of_nonneg_left
      (by have := (rate_range hμ hM).1; positivity) hμ hx0
    _ = _ := by ring

theorem inverseApprox_bound {μ M x : ℝ} (hμ : 0 < μ) (hM : μ < M)
    (hx0 : μ ≤ x) (hx1 : x ≤ M) (m : ℕ) :
    |(inverseApprox μ M m).eval x| ≤ 3 / μ := by
  have hx : 0 < x := lt_of_lt_of_le hμ hx0
  have hq := rate_range hμ hM
  have hp : (rate μ M) ^ m ≤ 1 := pow_le_one₀ hq.1.le hq.2.le
  have hi : (1 : ℝ) / x ≤ 1 / μ := one_div_le_one_div_of_le hμ hx0
  have herr := inverseApprox_error hμ hM hx0 hx1 m
  have htri := abs_add ((inverseApprox μ M m).eval x - 1 / x) (1 / x)
  rw [sub_add_cancel, abs_of_pos (one_div_pos.mpr hx)] at htri
  have hc : 0 < 2 / μ := by positivity
  have hmul := mul_le_mul_of_nonneg_left hp hc.le
  have hsum : (2 : ℝ) / μ + 1 / μ = 3 / μ := by ring
  linarith

/-- The actual Chebyshev inverse-polynomial lemma `zv:lem:polynomial`.
The witness is the explicit `inverseApprox μ M m`, so its coefficients depend
only on the public endpoints and the degree, not on the matrix or spectrum. -/
theorem exists_inverse_polynomial {μ M : ℝ} (hμ : 0 < μ) (hM : μ < M) (m : ℕ) :
    ∃ p : ℝ[X], p.natDegree ≤ m - 1 ∧
      ∀ x ∈ Set.Icc μ M,
        |p.eval x - 1 / x| ≤ (2 / μ) * (rate μ M) ^ m ∧ |p.eval x| ≤ 3 / μ := by
  refine ⟨inverseApprox μ M m, inverseApprox_degree μ M m, ?_⟩
  intro x hx
  exact ⟨inverseApprox_error hμ hM hx.1 hx.2 m, inverseApprox_bound hμ hM hx.1 hx.2 m⟩

end Bilevel.InversePolynomial
