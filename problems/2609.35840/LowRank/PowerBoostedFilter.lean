import LowRank.ChebyshevGapFilter

/-! Multiplying a filter by a normalized power preserves selected head
values while adding polynomial decay below them. The added degree is exact. -/

namespace LowRank
open Polynomial
noncomputable section

def powerBoostedFilter (f : ℝ[X]) (α : ℝ) (u : ℕ) : ℝ[X] := (C α⁻¹ * X) ^ u * f

theorem powerBoostedFilter_eval (f : ℝ[X]) (α x : ℝ) (u : ℕ) :
    (powerBoostedFilter f α u).eval x = (x / α) ^ u * f.eval x := by
  simp only [powerBoostedFilter, eval_mul, eval_pow, eval_C, eval_X, div_eq_mul_inv, mul_comm α⁻¹ x]

theorem powerBoostedFilter_natDegree_le (f : ℝ[X]) (α : ℝ) (u : ℕ) :
    (powerBoostedFilter f α u).natDegree ≤ f.natDegree + u := by
  have hbase : (C α⁻¹ * (X : ℝ[X])).natDegree ≤ 1 := by
    simpa only [natDegree_X] using natDegree_C_mul_le α⁻¹ (X : ℝ[X])
  have hp : ((C α⁻¹ * (X : ℝ[X])) ^ u).natDegree ≤ u := by
    simpa only [mul_one] using natDegree_pow_le_of_le u hbase
  exact natDegree_mul_le.trans (by omega)

theorem powerBoostedFilter_tail (f : ℝ[X]) {α L x η : ℝ} (u : ℕ)
    (hα : 0 < α) (hx : 0 ≤ x) (hxL : x ≤ L) (hη : 0 ≤ η) (hf : |f.eval x| ≤ η) :
    |(powerBoostedFilter f α u).eval x| ≤ η * (L / α) ^ u := by
  rw [powerBoostedFilter_eval, abs_mul, abs_of_nonneg (pow_nonneg (div_nonneg hx hα.le) u)]
  have hpow : (x / α) ^ u ≤ (L / α) ^ u :=
    pow_le_pow_left₀ (div_nonneg hx hα.le) (div_le_div_of_nonneg_right hxL hα.le) u
  calc
    _ ≤ (L / α) ^ u * η := mul_le_mul hpow hf (abs_nonneg _) (pow_nonneg (div_nonneg (hx.trans hxL) hα.le) u)
    _ = _ := mul_comm _ _

theorem powerBoostedFilter_retains (f : ℝ[X]) {α x : ℝ} (u : ℕ)
    (hα : 0 < α) (hx : α ≤ x) (hf : 1 ≤ f.eval x) :
    1 ≤ (powerBoostedFilter f α u).eval x := by
  rw [powerBoostedFilter_eval]
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ ((one_le_div hα).mpr hx)) hf

theorem powerBoostedChebyshev_spec {c α γ η : ℝ} (u : ℕ)
    (hc : 0 < c) (hα : 0 < α) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hη : 0 < η)
    (hgap : c * (1 + γ / 2) ≤ α) :
    let f := powerBoostedFilter (chebyshevGapFilter c γ (chebyshevFilterDegree γ η)) α u
    f.natDegree ≤ chebyshevFilterDegree γ η + u ∧
      (∀ x : ℝ, 0 ≤ x → x ≤ c → |f.eval x| ≤ η * (c / α) ^ u) ∧
      (∀ x : ℝ, α ≤ x → 1 ≤ f.eval x) := by
  have h := chebyshevGapFilter_spec hc hγ hγ1 hη
  refine ⟨(powerBoostedFilter_natDegree_le _ α u).trans (Nat.add_le_add_right h.1 u), ?_, ?_⟩
  · intro x hx hxc
    exact powerBoostedFilter_tail _ u hα hx hxc hη.le (h.2.1 x hx hxc)
  · intro x hx
    exact powerBoostedFilter_retains _ u hα hx (h.2.2 x (hgap.trans hx))

end
end LowRank
