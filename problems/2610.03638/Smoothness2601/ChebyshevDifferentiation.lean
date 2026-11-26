import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Polynomial differentiation on Chebyshev--Lobatto nodes

Actual Lagrange polynomials are used; their exactness is proved, not assumed.
The source's explicit rational weights are derived from the nodal polynomial
`(X² - 1) U_{2k}`, and their exact l1 norm is obtained from `T_{2k+1}`.
Parameter `k : ℕ` represents every odd degree as `n = 2k+1`.
-/

noncomputable section
open Polynomial Set
open scoped BigOperators

namespace Smoothness2601.ChebyshevDifferentiation

def node (n : ℕ) (i : Fin (n + 1)) : ℝ := Real.cos ((i.val : ℝ) * Real.pi / n)

theorem node_mem (n : ℕ) (i : Fin (n + 1)) : node n i ∈ Icc (-1) 1 :=
  ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

theorem angle_mem {n : ℕ} (hn : 0 < n) (i : Fin (n + 1)) :
    (i.val : ℝ) * Real.pi / n ∈ Icc 0 Real.pi := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  constructor
  · positivity
  · apply (div_le_iff₀ hnR).mpr
    have hi : (i.val : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
    nlinarith [Real.pi_pos]

theorem node_strictAnti {n : ℕ} (hn : 0 < n) : StrictAnti (node n) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  intro i j hij
  apply Real.cos_lt_cos_of_nonneg_of_le_pi (angle_mem hn i).1 (angle_mem hn j).2
  apply div_lt_div_of_pos_right _ hnR
  apply mul_lt_mul_of_pos_right _ Real.pi_pos
  exact_mod_cast hij

theorem node_ne_zero {n : ℕ} (hn : Odd n) (i : Fin (n + 1)) : node n i ≠ 0 := by
  have hn0 : 0 < n := hn.pos
  intro hz
  have hangle : (i.val : ℝ) * Real.pi / n = Real.pi / 2 := by
    apply Real.injOn_cos (angle_mem hn0 i)
      ⟨by positivity, by linarith [Real.pi_pos]⟩
    simpa only [Real.cos_pi_div_two] using hz
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn0)
  have he : (2 : ℝ) * i.val = n := by
    field_simp at hangle
    nlinarith [Real.pi_pos]
  have heN : 2 * i.val = n := by exact_mod_cast he
  obtain ⟨k, hk⟩ := hn
  omega

theorem chebyshev_at_node {n : ℕ} (hn : 0 < n) (i : Fin (n + 1)) :
    (Chebyshev.T ℝ n).eval (node n i) = (-1 : ℝ) ^ i.val := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [node, Chebyshev.T_real_cos]
  have he : ((n : ℤ) : ℝ) * ((i.val : ℝ) * Real.pi / n) = (i.val : ℝ) * Real.pi := by
    push_cast
    field_simp
  rw [he]
  simpa using Real.cos_nat_mul_pi_sub 0 i.val

theorem chebyshev_at_odd_node (k : ℕ) (i : Fin (2 * k + 2)) :
    (Chebyshev.T ℝ (2 * k + 1)).eval (node (2 * k + 1) i) = (-1 : ℝ) ^ i.val := by
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
    chebyshev_at_node (n := 2 * k + 1) (by omega) i

/-- Differentiation weights defined by actual Lagrange basis polynomials. -/
def interpolationWeight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) (i : ι) : ℝ := (Lagrange.basis Finset.univ v i).derivative.eval 0

theorem interpolation_exact {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) (hv : Function.Injective v) (P : Polynomial ℝ)
    (hdeg : P.degree < Fintype.card ι) :
    ∑ i, interpolationWeight v i * P.eval (v i) = P.derivative.eval 0 := by
  have he := Lagrange.eq_interpolate (s := Finset.univ) (v := v) hv.injOn
    (by simpa using hdeg)
  have hd := congrArg (fun Q : Polynomial ℝ => Q.derivative.eval 0) he
  simp only [Lagrange.interpolate_apply, derivative_sum, derivative_mul, derivative_C,
    zero_mul, zero_add, eval_finset_sum, eval_mul, eval_C] at hd
  simpa only [interpolationWeight, mul_comm] using hd.symm

def weight (n : ℕ) (h : ℝ) (i : Fin (n + 1)) : ℝ :=
  interpolationWeight (fun j => h * node n j) i

/-- Exact differentiation at arbitrary positive radius and arbitrary degree n.
Oddness is needed only for the explicit center-weight formula, not interpolation. -/
theorem exact_differentiation {n : ℕ} (hn : 0 < n) {h : ℝ} (hh : 0 < h)
    (P : Polynomial ℝ) (hdeg : P.natDegree ≤ n) :
    ∑ i, weight n h i * P.eval (h * node n i) = P.derivative.eval 0 := by
  apply interpolation_exact
  · intro i j he
    exact (node_strictAnti hn).injective (mul_left_cancel₀ hh.ne' he)
  · have hd : P.degree ≤ (n : WithBot ℕ) := (degree_le_natDegree).trans (by exact_mod_cast hdeg)
    exact hd.trans_lt (by exact_mod_cast (show n < Fintype.card (Fin (n + 1)) by simp))

theorem weights_sum_zero {n : ℕ} (hn : 0 < n) {h : ℝ} (hh : 0 < h) :
    ∑ i, weight n h i = 0 := by
  simpa using exact_differentiation hn hh (1 : Polynomial ℝ) (by simp)

theorem weights_linear_exact {n : ℕ} (hn : 0 < n) {h : ℝ} (hh : 0 < h) :
    ∑ i, weight n h i * (h * node n i) = 1 := by
  simpa using exact_differentiation hn hh (X : Polynomial ℝ) (by simpa using hn)

/-- A center weight derived from a vanishing polynomial. This lemma uses actual
polynomial factorization and interpolation; it postulates no weight identity. -/
theorem interpolationWeight_center {n : ℕ} (v : Fin (n + 1) → ℝ)
    (hv : Function.Injective v) (w : Polynomial ℝ) (hwdeg : w.natDegree ≤ n + 1)
    (hwroot : ∀ j, w.eval (v j) = 0) (hwcenter : w.derivative.eval 0 = 0)
    (i : Fin (n + 1)) (hvi : v i ≠ 0) (hdi : w.derivative.eval (v i) ≠ 0) :
    interpolationWeight v i = -w.eval 0 / (w.derivative.eval (v i) * (v i) ^ 2) := by
  have hw0 : w ≠ 0 := by intro hz; apply hdi; simp [hz]
  have hdvd : X - C (v i) ∣ w := (dvd_iff_isRoot).mpr (hwroot i)
  obtain ⟨q, hq⟩ := hdvd
  have hq0 : q ≠ 0 := by intro hz; apply hw0; simp [hq, hz]
  have hdegq : q.natDegree ≤ n := by
    have he : w.natDegree = 1 + q.natDegree := by
      rw [hq, natDegree_mul (X_sub_C_ne_zero _) hq0, natDegree_X_sub_C]
    omega
  have hq_eval : q.eval (v i) = w.derivative.eval (v i) := by
    simp [hq, derivative_mul]
  have hq_other : ∀ j, j ≠ i → q.eval (v j) = 0 := by
    intro j hji
    have he := hwroot j
    rw [hq, eval_mul, eval_sub, eval_X, eval_C] at he
    exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr (hv.ne hji))
  have hqd : interpolationWeight v i * w.derivative.eval (v i) = q.derivative.eval 0 := by
    have hdq : q.degree ≤ (n : WithBot ℕ) :=
      degree_le_natDegree.trans (by exact_mod_cast hdegq)
    have he := interpolation_exact v hv q (hdq.trans_lt
      (by exact_mod_cast (show n < Fintype.card (Fin (n + 1)) by simp)))
    rw [Finset.sum_eq_single i] at he
    · simpa only [hq_eval] using he
    · intro j _ hji
      rw [hq_other j hji, mul_zero]
    · simp
  have hval : w.eval 0 = -(v i) * q.eval 0 := by simp [hq]
  have hzero : q.eval 0 - v i * q.derivative.eval 0 = 0 := by
    simpa [hq, derivative_mul] using hwcenter
  apply (eq_div_iff (mul_ne_zero hdi (pow_ne_zero _ hvi))).mpr
  linear_combination (v i) ^ 2 * hqd - (v i) * hzero + hval

theorem chebyshevU_degree (n : ℕ) : (Chebyshev.U ℝ n).natDegree ≤ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [Chebyshev.U_one]
  | more n ih₀ ih₁ =>
    have heq : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by omega
    rw [heq, Chebyshev.U_add_two]
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · have hm := Polynomial.natDegree_mul_le
        (p := (2 : Polynomial ℝ) * X) (q := Chebyshev.U ℝ ((n : ℤ) + 1))
      have ht : (Chebyshev.U ℝ ((n : ℤ) + 1)).natDegree ≤ n + 1 := by simpa using ih₁
      have hl : ((2 : Polynomial ℝ) * X).natDegree ≤ 1 :=
        Polynomial.natDegree_mul_le.trans (by simp)
      omega
    · omega

def nodalPolynomial (k : ℕ) : Polynomial ℝ :=
  (X ^ 2 - 1) * Chebyshev.U ℝ (2 * k)

theorem nodalPolynomial_degree (k : ℕ) : (nodalPolynomial k).natDegree ≤ 2 * k + 2 := by
  have hu := chebyshevU_degree (2 * k)
  have hl : ((X : Polynomial ℝ) ^ 2 - 1).natDegree ≤ 2 :=
    (natDegree_sub_le _ _).trans (by simp)
  have hm := Polynomial.natDegree_mul_le (p := (X : Polynomial ℝ) ^ 2 - 1)
    (q := Chebyshev.U ℝ (2 * k))
  push_cast at hu
  unfold nodalPolynomial
  omega

theorem odd_angle (k : ℕ) :
    (((2 * k + 1 : ℕ) : ℤ) : ℝ) * (Real.pi / 2) = (k : ℝ) * Real.pi + Real.pi / 2 := by
  push_cast
  ring

theorem chebyshevT_center_odd (k : ℕ) : (Chebyshev.T ℝ (2 * k + 1)).eval 0 = 0 := by
  have he := Chebyshev.T_real_cos (Real.pi / 2) (2 * (k : ℤ) + 1)
  push_cast at he
  have ha : (2 * (k : ℝ) + 1) * (Real.pi / 2) =
      (k : ℝ) * Real.pi + Real.pi / 2 := by ring
  rw [ha] at he
  simpa [Real.cos_pi_div_two, Real.cos_add_pi_div_two, Real.sin_nat_mul_pi] using he

theorem chebyshevU_center_even (k : ℕ) :
    (Chebyshev.U ℝ (2 * k)).eval 0 = (-1 : ℝ) ^ k := by
  have he := Chebyshev.U_real_cos (Real.pi / 2) (2 * (k : ℤ))
  push_cast at he
  have ha : (2 * (k : ℝ) + 1) * (Real.pi / 2) =
      (k : ℝ) * Real.pi + Real.pi / 2 := by ring
  rw [ha, Real.sin_add_pi_div_two] at he
  have hc : Real.cos ((k : ℝ) * Real.pi) = (-1 : ℝ) ^ k := by
    simpa using Real.cos_nat_mul_pi_sub 0 k
  simpa [Real.cos_pi_div_two, Real.sin_pi_div_two] using
    he.trans hc

theorem nodalPolynomial_center (k : ℕ) :
    (nodalPolynomial k).eval 0 = -((-1 : ℝ) ^ k) := by
  simp [nodalPolynomial, chebyshevU_center_even]

theorem nodalPolynomial_derivative (k : ℕ) :
    (nodalPolynomial k).derivative = X * Chebyshev.U ℝ (2 * k) +
      (2 * (k : Polynomial ℝ) + 1) * Chebyshev.T ℝ (2 * k + 1) := by
  have he := Chebyshev.add_one_mul_T_eq_poly_in_U (R := ℝ) (2 * (k : ℤ))
  push_cast at he
  unfold nodalPolynomial
  simp only [derivative_mul, derivative_sub, derivative_pow, derivative_X,
    derivative_one, sub_zero, mul_one, Nat.cast_ofNat, map_ofNat, pow_one]
  linear_combination -he

theorem nodalPolynomial_derivative_center (k : ℕ) :
    (nodalPolynomial k).derivative.eval 0 = 0 := by
  simp [nodalPolynomial_derivative, chebyshevT_center_odd]

theorem node_first {n : ℕ} (i : Fin (n + 1)) (hi : i.val = 0) : node n i = 1 := by
  simp [node, hi]

theorem node_last {n : ℕ} (hn : 0 < n) (i : Fin (n + 1)) (hi : i.val = n) :
    node n i = -1 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  simp [node, hi, mul_div_cancel_left₀ Real.pi hnR]

theorem chebyshevU_interior (k : ℕ) (i : Fin (2 * k + 2))
    (hi0 : 0 < i.val) (hi1 : i.val < 2 * k + 1) :
    (Chebyshev.U ℝ (2 * k)).eval (node (2 * k + 1) i) = 0 := by
  have hnR : (0 : ℝ) < (2 * k + 1 : ℕ) := by positivity
  have ha0 : 0 < (i.val : ℝ) * Real.pi / (2 * k + 1 : ℕ) := by
    exact div_pos (mul_pos (by exact_mod_cast hi0) Real.pi_pos) hnR
  have ha1 : (i.val : ℝ) * Real.pi / (2 * k + 1 : ℕ) < Real.pi := by
    apply (div_lt_iff₀ hnR).mpr
    simpa only [mul_comm] using mul_lt_mul_of_pos_right
      (show (i.val : ℝ) < (2 * k + 1 : ℕ) by exact_mod_cast hi1) Real.pi_pos
  have hs := Real.sin_pos_of_pos_of_lt_pi ha0 ha1
  have he := Chebyshev.U_real_cos ((i.val : ℝ) * Real.pi / (2 * k + 1 : ℕ))
    (2 * (k : ℤ))
  push_cast at he
  have hm : (2 * (k : ℝ) + 1) *
      ((i.val : ℝ) * Real.pi / (2 * (k : ℝ) + 1)) = (i.val : ℝ) * Real.pi := by
    field_simp
  rw [hm, Real.sin_nat_mul_pi] at he
  apply (mul_eq_zero.mp (show (Chebyshev.U ℝ (2 * k)).eval (node (2 * k + 1) i) *
      Real.sin ((i.val : ℝ) * Real.pi / (2 * k + 1 : ℕ)) = 0 from by
        simpa only [node, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using he)).resolve_right hs.ne'

theorem nodalPolynomial_roots (k : ℕ) (i : Fin (2 * k + 2)) :
    (nodalPolynomial k).eval (node (2 * k + 1) i) = 0 := by
  by_cases hfirst : i.val = 0
  · simp [node_first i hfirst, nodalPolynomial]
  by_cases hlast : i.val = 2 * k + 1
  · simp [node_last (by omega) i hlast, nodalPolynomial]
  · simp [nodalPolynomial, chebyshevU_interior k i (by omega) (by omega)]

def endpointFactor (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  if i.val = 0 ∨ i.val = n then 2 else 1

theorem endpointFactor_pos (n : ℕ) (i : Fin (n + 1)) : 0 < endpointFactor n i := by
  unfold endpointFactor
  split_ifs <;> norm_num

theorem nodalPolynomial_derivative_node (k : ℕ) (i : Fin (2 * k + 2)) :
    (nodalPolynomial k).derivative.eval (node (2 * k + 1) i) =
      (2 * k + 1 : ℕ) * endpointFactor (2 * k + 1) i * (-1 : ℝ) ^ i.val := by
  by_cases hfirst : i.val = 0
  · simp [nodalPolynomial_derivative, node_first i hfirst, endpointFactor, hfirst]
    ring
  by_cases hlast : i.val = 2 * k + 1
  · simp [nodalPolynomial_derivative, node_last (by omega) i hlast, endpointFactor, hlast,
      Int.negOnePow_two_mul, Int.negOnePow_two_mul_add_one, pow_add, pow_mul]
    ring
  · simp [nodalPolynomial_derivative, endpointFactor, hfirst, hlast,
      chebyshevU_interior k i (by omega) (by omega),
      chebyshev_at_odd_node]

theorem nodalPolynomial_derivative_node_ne_zero (k : ℕ) (i : Fin (2 * k + 2)) :
    (nodalPolynomial k).derivative.eval (node (2 * k + 1) i) ≠ 0 := by
  rw [nodalPolynomial_derivative_node]
  exact mul_ne_zero (mul_ne_zero (by positivity) (endpointFactor_pos _ _).ne')
    (pow_ne_zero _ (by norm_num))

/-- The exact source formula, parameterized by odd degree n = 2k+1. -/
def explicitWeight (k : ℕ) (h : ℝ) (i : Fin (2 * k + 2)) : ℝ :=
  ((-1 : ℝ) ^ k * (-1 : ℝ) ^ i.val) /
    ((2 * k + 1 : ℕ) * h * endpointFactor (2 * k + 1) i * node (2 * k + 1) i ^ 2)

theorem explicitWeight_eq_interpolationWeight (k : ℕ) (i : Fin (2 * k + 2)) :
    explicitWeight k 1 i = interpolationWeight (node (2 * k + 1)) i := by
  have hi : node (2 * k + 1) i ≠ 0 := node_ne_zero (by exact ⟨k, by omega⟩) i
  rw [interpolationWeight_center _ (node_strictAnti (by omega)).injective
    (nodalPolynomial k) (by simpa using nodalPolynomial_degree k)
    (nodalPolynomial_roots k) (nodalPolynomial_derivative_center k) i hi
    (nodalPolynomial_derivative_node_ne_zero k i),
    nodalPolynomial_center, nodalPolynomial_derivative_node]
  unfold explicitWeight
  simp only [mul_one, neg_neg, div_eq_mul_inv, mul_inv_rev, ← inv_pow, inv_neg, inv_one]
  ring

theorem explicitWeight_scale (k : ℕ) (h : ℝ) (i : Fin (2 * k + 2)) :
    explicitWeight k h i = explicitWeight k 1 i / h := by
  simp only [explicitWeight, div_eq_mul_inv, mul_inv_rev, one_mul, mul_one]
  ring

theorem explicit_differentiation (k : ℕ) {h : ℝ} (hh : 0 < h)
    (P : Polynomial ℝ) (hdeg : P.natDegree ≤ 2 * k + 1) :
    ∑ i, explicitWeight k h i * P.eval (h * node (2 * k + 1) i) =
      P.derivative.eval 0 := by
  let Q := P.comp (C h * X)
  have hQ : Q.natDegree ≤ 2 * k + 1 := by
    have hin : (C h * (X : Polynomial ℝ)).natDegree ≤ 1 :=
      (natDegree_C_mul_le h X).trans (by simp)
    exact (natDegree_comp_le.trans (Nat.mul_le_mul_left _ hin)).trans (by simpa using hdeg)
  have hinterp := interpolation_exact (node (2 * k + 1))
    (node_strictAnti (by omega)).injective Q
    ((degree_le_natDegree.trans (show (Q.natDegree : WithBot ℕ) ≤ (2 * k + 1 : ℕ) by
      exact_mod_cast hQ)).trans_lt
      (by exact_mod_cast (show 2 * k + 1 < Fintype.card (Fin (2 * k + 2)) by simp)))
  have he : (∑ i, explicitWeight k 1 i * P.eval (h * node (2 * k + 1) i)) =
      P.derivative.eval 0 * h := by
    simp only [Q, derivative_comp, derivative_mul, derivative_C, derivative_X,
      zero_mul, zero_add, mul_one, eval_comp, eval_mul, eval_C, eval_X,
      mul_zero] at hinterp
    simp only [explicitWeight_eq_interpolationWeight]
    simpa only [mul_comm] using hinterp
  simp_rw [explicitWeight_scale k h]
  calc
    _ = (∑ i, explicitWeight k 1 i * P.eval (h * node (2 * k + 1) i)) / h := by
      simp only [div_eq_mul_inv]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [he, mul_div_cancel_right₀ _ hh.ne']

theorem explicit_weights_sum_zero (k : ℕ) {h : ℝ} (hh : 0 < h) :
    ∑ i, explicitWeight k h i = 0 := by
  simpa using explicit_differentiation k hh (1 : Polynomial ℝ) (by simp)

theorem chebyshevT_degree (n : ℕ) : (Chebyshev.T ℝ n).natDegree ≤ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih₀ ih₁ =>
    have heq : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by omega
    rw [heq, Chebyshev.T_add_two]
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · have hm := Polynomial.natDegree_mul_le
        (p := (2 : Polynomial ℝ) * X) (q := Chebyshev.T ℝ ((n : ℤ) + 1))
      have ht : (Chebyshev.T ℝ ((n : ℤ) + 1)).natDegree ≤ n + 1 := by simpa using ih₁
      have hl : ((2 : Polynomial ℝ) * X).natDegree ≤ 1 :=
        Polynomial.natDegree_mul_le.trans (by simp)
      omega
    · omega

theorem chebyshevT_derivative_center (k : ℕ) :
    (Chebyshev.T ℝ (2 * k + 1)).derivative.eval 0 =
      (2 * k + 1 : ℕ) * (-1 : ℝ) ^ k := by
  simp [Chebyshev.T_derivative_eq_U, chebyshevU_center_even]

theorem explicitWeight_abs_unit (k : ℕ) (i : Fin (2 * k + 2)) :
    |explicitWeight k 1 i| = (-1 : ℝ) ^ k * explicitWeight k 1 i * (-1 : ℝ) ^ i.val := by
  have hden : 0 < (2 * k + 1 : ℕ) * endpointFactor (2 * k + 1) i *
      node (2 * k + 1) i ^ 2 := by
    exact mul_pos (mul_pos (by positivity) (endpointFactor_pos _ _))
      (sq_pos_of_ne_zero (node_ne_zero (by exact ⟨k, by omega⟩) i))
  have hk : ((-1 : ℝ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm k 2, pow_mul]; norm_num
  have hi : ((-1 : ℝ) ^ i.val) ^ 2 = 1 := by rw [← pow_mul, mul_comm i.val 2, pow_mul]; norm_num
  calc
    _ = 1 / ((2 * k + 1 : ℕ) * endpointFactor (2 * k + 1) i *
        node (2 * k + 1) i ^ 2) := by
      simp only [explicitWeight, mul_one, abs_div, abs_mul, abs_pow,
        abs_neg, abs_one, one_pow, one_mul, abs_of_pos hden]
    _ = (((-1 : ℝ) ^ k) ^ 2 * ((-1 : ℝ) ^ i.val) ^ 2) /
        ((2 * k + 1 : ℕ) * endpointFactor (2 * k + 1) i * node (2 * k + 1) i ^ 2) := by
      rw [hk, hi, mul_one]
    _ = _ := by unfold explicitWeight; ring

/-- Exact l1 norm n/h, with every node and weight explicitly defined. -/
theorem explicit_weights_abs_sum (k : ℕ) {h : ℝ} (hh : 0 < h) :
    ∑ i, |explicitWeight k h i| = (2 * k + 1 : ℕ) / h := by
  have hunit : (∑ i, |explicitWeight k 1 i|) = (2 * k + 1 : ℕ) := by
    simp_rw [explicitWeight_abs_unit]
    have he := explicit_differentiation k (by norm_num : (0 : ℝ) < 1)
      (Chebyshev.T ℝ (2 * k + 1)) (chebyshevT_degree (2 * k + 1))
    simp only [one_mul, chebyshev_at_odd_node,
      chebyshevT_derivative_center] at he
    calc
      _ = (-1 : ℝ) ^ k * ∑ i, explicitWeight k 1 i * (-1 : ℝ) ^ i.val := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (-1 : ℝ) ^ k * ((2 * k + 1 : ℕ) * (-1 : ℝ) ^ k) := by rw [he]
      _ = (2 * k + 1 : ℕ) := by
        have hs : ((-1 : ℝ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm k 2, pow_mul]; norm_num
        nlinarith
  simp_rw [explicitWeight_scale k h, abs_div, abs_of_pos hh]
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, hunit]

/-- Coordinatewise vector-polynomial version, covering every finite Euclidean
output dimension used by the manuscript's gradient fields. -/
theorem explicit_differentiation_vector {ι : Type*} (k : ℕ) {h : ℝ} (hh : 0 < h)
    (P : ι → Polynomial ℝ) (hdeg : ∀ j, (P j).natDegree ≤ 2 * k + 1) :
    (∑ i, explicitWeight k h i • (fun j => (P j).eval (h * node (2 * k + 1) i))) =
      (fun j => (P j).derivative.eval 0) := by
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact explicit_differentiation k hh (P j) (hdeg j)

/-- All three identities in source Lemma `lem:cheb`, for n=2k+1 and h>0. -/
theorem odd_chebyshev_differentiation (k : ℕ) {h : ℝ} (hh : 0 < h) :
    (∀ i : Fin (2 * k + 2), node (2 * k + 1) i ≠ 0) ∧
    (∀ P : Polynomial ℝ, P.natDegree ≤ 2 * k + 1 →
      ∑ i, explicitWeight k h i * P.eval (h * node (2 * k + 1) i) = P.derivative.eval 0) ∧
    (∑ i, explicitWeight k h i = 0) ∧
    (∑ i, |explicitWeight k h i| = (2 * k + 1 : ℕ) / h) :=
  ⟨node_ne_zero (by exact ⟨k, by omega⟩), explicit_differentiation k hh,
    explicit_weights_sum_zero k hh, explicit_weights_abs_sum k hh⟩

end Smoothness2601.ChebyshevDifferentiation
