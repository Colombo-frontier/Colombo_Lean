import LowRank.ChebyshevBounds
import Mathlib.Data.Real.Archimedean

/-! An explicit polynomial that suppresses [0,t] while retaining the
spectrum above t*(1+gamma/2). Its sufficient degree is logarithmic in
inverse tail tolerance and proportional to inverse square root gap. -/

namespace LowRank
open Polynomial
noncomputable section

def chebyshevGapFilter (t γ : ℝ) (n : ℕ) : ℝ[X] :=
  C ((Chebyshev.T ℝ (n : ℤ)).eval (1 + γ))⁻¹ *
    (Chebyshev.T ℝ (n : ℤ)).comp (C (2 / t) * X - 1)

theorem chebyshevGapFilter_eval (t γ x : ℝ) (n : ℕ) :
    (chebyshevGapFilter t γ n).eval x =
      (Chebyshev.T ℝ (n : ℤ)).eval (2 * x / t - 1) /
        (Chebyshev.T ℝ (n : ℤ)).eval (1 + γ) := by
  simp only [chebyshevGapFilter, eval_mul, eval_C, eval_comp, eval_sub, eval_X, eval_one]
  rw [show 2 / t * x - 1 = 2 * x / t - 1 by ring]
  simp only [div_eq_mul_inv]
  rw [mul_comm]

theorem chebyshevGapFilter_natDegree_le (t γ : ℝ) (n : ℕ) :
    (chebyshevGapFilter t γ n).natDegree ≤ n := by
  apply (natDegree_C_mul_le _ _).trans
  apply natDegree_comp_le.trans
  have hlin : (C (2 / t) * X - (1 : ℝ[X])).natDegree ≤ 1 := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact (natDegree_C_mul_le _ _).trans (by simp)
    · simp
  calc
    _ ≤ n * 1 := Nat.mul_le_mul (chebyshev_natDegree_le n) hlin
    _ = n := Nat.mul_one n

theorem chebyshevGapFilter_tail (n : ℕ) {t γ x : ℝ} (ht : 0 < t)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hx : 0 ≤ x) (hxt : x ≤ t) :
    |(chebyshevGapFilter t γ n).eval x| ≤ 2 * Real.exp (-((n : ℝ) * Real.sqrt γ / 2)) := by
  rw [chebyshevGapFilter_eval]
  apply chebyshev_eval_gap_ratio n hγ hγ1
  · have hdiv : 0 ≤ 2 * x / t := div_nonneg (by positivity) ht.le
    linarith
  · have hdiv : 2 * x / t ≤ 2 := (div_le_iff₀ ht).mpr (by linarith)
    linarith
  · exact le_rfl

theorem chebyshevGapFilter_retains (n : ℕ) {t γ x : ℝ} (ht : 0 < t)
    (hγ : 0 ≤ γ) (hx : t * (1 + γ / 2) ≤ x) :
    1 ≤ (chebyshevGapFilter t γ n).eval x := by
  rw [chebyshevGapFilter_eval]
  have harg : 1 + γ ≤ 2 * x / t - 1 := by
    have hdiv : 2 + γ ≤ 2 * x / t := (le_div_iff₀ ht).mpr (by nlinarith)
    linarith
  have hden : 0 < (Chebyshev.T ℝ (n : ℤ)).eval (1 + γ) :=
    lt_of_lt_of_le (by norm_num) (chebyshev_eval_ge_one n (by linarith))
  apply (le_div_iff₀ hden).mpr
  simpa only [one_mul] using chebyshev_eval_mono n (by linarith : 1 ≤ 1 + γ) harg

theorem chebyshev_tail_tolerance (n : ℕ) {γ η : ℝ} (hγ : 0 < γ) (hη : 0 < η)
    (hn : 2 * Real.log (2 / η) / Real.sqrt γ ≤ (n : ℝ)) :
    2 * Real.exp (-((n : ℝ) * Real.sqrt γ / 2)) ≤ η := by
  have hs : 0 < Real.sqrt γ := Real.sqrt_pos.mpr hγ
  have hlog : Real.log (2 / η) ≤ (n : ℝ) * Real.sqrt γ / 2 := by
    have h := (div_le_iff₀ hs).mp hn
    linarith
  calc
    _ ≤ 2 * Real.exp (-Real.log (2 / η)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hlog)) (by norm_num)
    _ = η := by
      rw [Real.exp_neg, Real.exp_log (div_pos (by norm_num) hη)]
      field_simp

def chebyshevFilterDegree (γ η : ℝ) : ℕ := ⌈2 * Real.log (2 / η) / Real.sqrt γ⌉₊

theorem chebyshevFilterDegree_le {γ η : ℝ} (hγ : 0 < γ) (hη : 0 < η) (hη1 : η ≤ 1) :
    (chebyshevFilterDegree γ η : ℝ) < 2 * Real.log (2 / η) / Real.sqrt γ + 1 := by
  apply Nat.ceil_lt_add_one
  apply div_nonneg _ (Real.sqrt_pos.mpr hγ).le
  apply mul_nonneg (by norm_num)
  apply Real.log_nonneg
  exact (le_div_iff₀ hη).mpr (by linarith)

theorem chebyshevGapFilter_spec {t γ η : ℝ} (ht : 0 < t)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hη : 0 < η) :
    let f := chebyshevGapFilter t γ (chebyshevFilterDegree γ η)
    f.natDegree ≤ chebyshevFilterDegree γ η ∧
      (∀ x : ℝ, 0 ≤ x → x ≤ t → |f.eval x| ≤ η) ∧
      (∀ x : ℝ, t * (1 + γ / 2) ≤ x → 1 ≤ f.eval x) := by
  refine ⟨chebyshevGapFilter_natDegree_le _ _ _, ?_, ?_⟩
  · intro x hx hxt
    exact (chebyshevGapFilter_tail _ ht hγ.le hγ1 hx hxt).trans
      (chebyshev_tail_tolerance _ hγ hη (Nat.le_ceil _))
  · intro x hx
    exact chebyshevGapFilter_retains _ ht hγ.le hx

end
end LowRank
