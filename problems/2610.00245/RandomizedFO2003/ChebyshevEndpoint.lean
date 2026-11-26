import RandomizedFO2003.AlternatingRoots
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev

namespace RandomizedFO2003

open Polynomial Set

noncomputable def lobattoNode (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  Real.cos ((i.val : ℝ) * Real.pi / n)

theorem lobatto_mem (n : ℕ) (i : Fin (n + 1)) : lobattoNode n i ∈ Icc (-1) 1 :=
  ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

theorem lobatto_strictAnti (n : ℕ) (hn : 0 < n) : StrictAnti (lobattoNode n) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  intro i j hij
  apply Real.cos_lt_cos_of_nonneg_of_le_pi
  · positivity
  · apply (div_le_iff₀ hnR).mpr
    have hj : (j.val : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt_succ j.isLt)
    nlinarith [Real.pi_pos]
  · apply div_lt_div_of_pos_right _ hnR
    apply mul_lt_mul_of_pos_right _ Real.pi_pos
    exact_mod_cast hij

theorem chebyshev_lobatto (n : ℕ) (hn : 0 < n) (i : Fin (n + 1)) :
    (Chebyshev.T ℝ n).eval (lobattoNode n i) = (-1 : ℝ) ^ i.val := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [lobattoNode, Chebyshev.T_real_cos]
  have h : ((n : ℤ) : ℝ) * ((i.val : ℝ) * Real.pi / n) = (i.val : ℝ) * Real.pi := by
    push_cast
    field_simp
  rw [h]
  simpa using Real.cos_nat_mul_pi_sub 0 i.val

theorem chebyshev_natDegree_le (n : ℕ) : (Chebyshev.T ℝ n).natDegree ≤ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih₀ ih₁ =>
    have heq : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by omega
    rw [heq, Chebyshev.T_add_two]
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · have hmul := Polynomial.natDegree_mul_le
        (p := (2 : Polynomial ℝ) * X) (q := Chebyshev.T ℝ ((n : ℤ) + 1))
      have ht : (Chebyshev.T ℝ ((n : ℤ) + 1)).natDegree ≤ n + 1 := by simpa using ih₁
      have hleft : ((2 : Polynomial ℝ) * X).natDegree ≤ 1 := by
        exact (Polynomial.natDegree_mul_le).trans (by simp)
      omega
    · omega

theorem chebyshev_derivative_one (n : ℕ) :
    (Chebyshev.T ℝ n).derivative.eval 1 = (n : ℝ) ^ 2 := by
  simp [Chebyshev.T_derivative_eq_U, Chebyshev.U_eval_one]
  ring

private theorem alternating_error_sign (a b c u : ℝ)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hc : 1 < c) (hu : u ^ 2 = 1) :
    (a + c * u) * (b - c * u) < 0 := by
  have hz : (u - 1) * (u + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hz with h | h
  · have he : u = 1 := by linarith
    rw [he, mul_one]
    exact mul_neg_of_pos_of_neg (by linarith [(abs_le.mp ha).1])
      (by linarith [(abs_le.mp hb).2])
  · have he : u = -1 := by linarith
    rw [he]
    apply mul_neg_of_neg_of_pos
    · linarith [(abs_le.mp ha).2]
    · linarith [(abs_le.mp hb).1]

/-- The endpoint Markov inequality on [-1,1], proved through alternation and
Rolle root counting. No polynomial derivative inequality is assumed. -/
theorem polynomial_derivative_one_le (n : ℕ) (hn : 0 < n) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ n) (hbound : ∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) :
    p.derivative.eval 1 ≤ (n : ℝ) ^ 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  by_contra hnot
  have hbig : ((k + 1 : ℕ) : ℝ) ^ 2 < p.derivative.eval 1 := lt_of_not_ge hnot
  let c : ℝ := p.derivative.eval 1 / ((k + 1 : ℕ) : ℝ) ^ 2
  have hnR : 0 < ((k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have hc : 1 < c := (lt_div_iff₀ hnR).mpr (by simpa using hbig)
  let q : Polynomial ℝ := p - C c * Chebyshev.T ℝ (k + 1 : ℕ)
  have hdeg : q.natDegree ≤ k + 1 := by
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le hp
      ((Polynomial.natDegree_C_mul_le _ _).trans (chebyshev_natDegree_le _)))
  have hqder : q.derivative.eval 1 = 0 := by
    simp only [q, derivative_sub, derivative_mul, derivative_C, zero_mul, zero_add,
      eval_sub, eval_mul, eval_C, chebyshev_derivative_one]
    dsimp [c]
    field_simp
  apply derivative_ne_zero_of_alternating_nodes k q (lobattoNode (k + 1)) 1
    (lobatto_strictAnti _ (by omega)) (fun i => (lobatto_mem _ i).2) hdeg _ hqder
  intro i
  have hpow : ((-1 : ℝ) ^ i.val) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hs := alternating_error_sign (p.eval (lobattoNode (k + 1) i.succ))
    (p.eval (lobattoNode (k + 1) i.castSucc)) c ((-1 : ℝ) ^ i.val)
    (hbound _ (lobatto_mem _ _)) (hbound _ (lobatto_mem _ _)) hc hpow
  simp only [q, eval_sub, eval_mul, eval_C]
  rw [chebyshev_lobatto (k + 1) (by omega) i.succ,
    chebyshev_lobatto (k + 1) (by omega) i.castSucc]
  simpa [pow_succ, mul_neg] using hs

theorem abs_polynomial_derivative_one_le (n : ℕ) (hn : 0 < n) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ n) (hbound : ∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) :
    |p.derivative.eval 1| ≤ (n : ℝ) ^ 2 := by
  apply abs_le.mpr
  constructor
  · have h := polynomial_derivative_one_le n hn (-p) (by simpa using hp)
      (by simpa using hbound)
    simpa using neg_le_neg h
  · exact polynomial_derivative_one_le n hn p hp hbound

end RandomizedFO2003
