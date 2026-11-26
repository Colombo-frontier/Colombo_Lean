import RandomizedFO2003.ChebyshevEndpoint
import Mathlib.Algebra.Polynomial.Degree.Lemmas

namespace RandomizedFO2003

open Polynomial Set

theorem abs_derivative_one_le_mul (n : ℕ) (hn : 0 < n) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ n) (B : ℝ) (hB : 0 < B)
    (hbound : ∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ B) :
    |p.derivative.eval 1| ≤ (n : ℝ) ^ 2 * B := by
  let q : Polynomial ℝ := C B⁻¹ * p
  have hqdeg : q.natDegree ≤ n := (Polynomial.natDegree_C_mul_le _ _).trans hp
  have hqbound : ∀ x ∈ Icc (-1 : ℝ) 1, |q.eval x| ≤ 1 := by
    intro x hx
    simp only [q, eval_mul, eval_C, abs_mul, abs_of_pos (inv_pos.mpr hB)]
    calc
      B⁻¹ * |p.eval x| ≤ B⁻¹ * B := mul_le_mul_of_nonneg_left (hbound x hx) (inv_pos.mpr hB).le
      _ = 1 := inv_mul_cancel₀ hB.ne'
  have h := abs_polynomial_derivative_one_le n hn q hqdeg hqbound
  have hdiv : |p.derivative.eval 1| / B ≤ (n : ℝ) ^ 2 := by
    simpa [q, derivative_mul, abs_mul, abs_of_pos (inv_pos.mpr hB), div_eq_mul_inv,
      mul_comm] using h
  exact (div_le_iff₀ hB).mp hdiv

theorem affine_derivative_endpoint_bound (n : ℕ) (hn : 0 < n) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ n) (B u v : ℝ) (hB : 0 < B)
    (hbound : ∀ t ∈ Icc (-1 : ℝ) 1, |p.eval (u * t + v)| ≤ B) :
    |u| * |p.derivative.eval (u + v)| ≤ (n : ℝ) ^ 2 * B := by
  let a : Polynomial ℝ := C u * X + C v
  have hadeg : a.natDegree ≤ 1 := by
    apply (Polynomial.natDegree_add_le _ _).trans
    exact max_le ((Polynomial.natDegree_C_mul_le _ _).trans (by simp)) (by simp)
  have hqdeg : (p.comp a).natDegree ≤ n := by
    calc
      (p.comp a).natDegree ≤ p.natDegree * a.natDegree := Polynomial.natDegree_comp_le
      _ ≤ p.natDegree * 1 := Nat.mul_le_mul_left _ hadeg
      _ ≤ n := by simpa using hp
  have h := abs_derivative_one_le_mul n hn (p.comp a) hqdeg B hB (by
    intro t ht
    simpa [a] using hbound t ht)
  simpa [a, derivative_comp, derivative_add, derivative_mul, abs_mul] using h

theorem derivative_left_interval_bound (n : ℕ) (hn : 0 < n) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ n) (a b B : ℝ) (hab : a ≤ b) (hB : 0 < B)
    (hbound : ∀ x ∈ Icc a b, |p.eval x| ≤ B) :
    |p.derivative.eval a| * (b - a) ≤ 2 * (n : ℝ) ^ 2 * B := by
  have h := affine_derivative_endpoint_bound n hn p hp B ((a - b) / 2) ((a + b) / 2) hB (by
    intro t ht
    apply hbound
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr ht.2)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hab) (show 0 ≤ t + 1 by linarith [ht.1])])
  rw [show (a - b) / 2 + (a + b) / 2 = a by ring,
    abs_of_nonpos (by linarith : (a - b) / 2 ≤ 0)] at h
  nlinarith

theorem derivative_right_interval_bound (n : ℕ) (hn : 0 < n) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ n) (a b B : ℝ) (hab : a ≤ b) (hB : 0 < B)
    (hbound : ∀ x ∈ Icc a b, |p.eval x| ≤ B) :
    |p.derivative.eval b| * (b - a) ≤ 2 * (n : ℝ) ^ 2 * B := by
  have h := affine_derivative_endpoint_bound n hn p hp B ((b - a) / 2) ((a + b) / 2) hB (by
    intro t ht
    apply hbound
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr hab) (show 0 ≤ t + 1 by linarith [ht.1])]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr ht.2)])
  rw [show (b - a) / 2 + (a + b) / 2 = b by ring,
    abs_of_nonneg (by linarith : 0 ≤ (b - a) / 2)] at h
  nlinarith

/-- A global polynomial Markov bound with a factor 4 rather than the optimal 2.
The constant is sufficient for the inverse-approximation obstruction. -/
theorem polynomial_markov_interval (n : ℕ) (hn : 0 < n) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ n) (a b B : ℝ) (hab : a < b) (hB : 0 < B)
    (hbound : ∀ x ∈ Icc a b, |p.eval x| ≤ B) :
    ∀ x ∈ Icc a b, |p.derivative.eval x| ≤ 4 * (n : ℝ) ^ 2 * B / (b - a) := by
  intro x hx
  apply (le_div_iff₀ (sub_pos.mpr hab)).mpr
  by_cases hmid : x ≤ (a + b) / 2
  · have h := derivative_left_interval_bound n hn p hp x b B hx.2 hB
      (fun y hy => hbound y ⟨hx.1.trans hy.1, hy.2⟩)
    nlinarith [mul_nonneg (abs_nonneg (p.derivative.eval x))
      (show 0 ≤ b - x - (b - a) / 2 by linarith)]
  · have h := derivative_right_interval_bound n hn p hp a x B hx.1 hB
      (fun y hy => hbound y ⟨hy.1, hy.2.trans hx.2⟩)
    nlinarith [mul_nonneg (abs_nonneg (p.derivative.eval x))
      (show 0 ≤ x - a - (b - a) / 2 by linarith)]

end RandomizedFO2003
