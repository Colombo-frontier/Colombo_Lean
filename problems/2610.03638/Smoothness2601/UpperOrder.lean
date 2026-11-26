import Smoothness2601.OrderTradeoff
import Mathlib.Tactic

/-! One finite near-minimizing order with uniform logarithmic size, for every
finite or infinite cap. No attainment of the infimum is assumed. -/
noncomputable section
namespace Smoothness2601.UpperOrder

def cap (ε : ℝ) : ℕ := ⌈Real.log (1/ε)⌉₊

theorem cap_pos {ε : ℝ} (ht : 1 ≤ Real.log (1/ε)) : 1 ≤ cap ε := by
  exact_mod_cast ht.trans (Nat.le_ceil _)

theorem truncate_score {β ε : ℝ} (hβ : 0 ≤ β) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ht : 1 ≤ Real.log (1/ε)) (r : ℕ) (hr : 1 ≤ r) :
    orderTerm β ε (min r (cap ε)) ≤ Real.exp 1*orderTerm β ε r := by
  by_cases hrc : r ≤ cap ε
  · rw [min_eq_left hrc]
    exact le_mul_of_one_le_left (orderTerm_pos hε hr).le
      (Real.one_le_exp_iff.mpr (by norm_num))
  · have hcr : cap ε ≤ r := (lt_of_not_ge hrc).le
    rw [min_eq_right hcr]
    have hc := (orderTerm_zero_log_ceil hε ht).1
    have hpow : (cap ε:ℝ) ^ β ≤ (r:ℝ) ^ β :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hcr) hβ
    have hfac : 1 ≤ ε ^ (-1/(r:ℝ)) := by
      simpa only [orderTerm,Real.rpow_zero,one_mul] using orderTerm_one_le (β := 0) (by norm_num) hε hε1 hr
    calc
      orderTerm β ε (cap ε) = (cap ε:ℝ) ^ β*orderTerm 0 ε (cap ε) := by simp only [orderTerm,Real.rpow_zero,one_mul]
      _ ≤ (r:ℝ) ^ β*Real.exp 1 := mul_le_mul hpow hc (orderTerm_pos hε (cap_pos ht)).le
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ ≤ (r:ℝ) ^ β*(Real.exp 1*ε ^ (-1/(r:ℝ))) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (Real.exp_pos _).le hfac)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = _ := by unfold orderTerm; ring

/-- Uniformly in p and β≥0, an actual finite order is within 2e of the
order-tradeoff infimum and is no larger than 2 log(1/ε). -/
theorem finite_near_minimizer {p : WithTop ℕ} {β ε : ℝ}
    (hp : 1 ≤ p) (hβ : 0 ≤ β) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ht : 1 ≤ Real.log (1/ε)) :
    ∃ r : ℕ, 1 ≤ r ∧ (r:WithTop ℕ) ≤ p ∧ (r:ℝ) ≤ 2*Real.log (1/ε) ∧
      orderTerm β ε r ≤ (2*Real.exp 1)*orderTradeoff p β ε := by
  have hD := orderTradeoff_one_le hp hβ hε hε1
  have hlt : orderTradeoff p β ε < 2*orderTradeoff p β ε := by linarith
  obtain ⟨_,⟨r,hr,rfl⟩,hscore⟩ := exists_lt_of_csInf_lt
    ((availableOrders_nonempty hp).image (orderTerm β ε)) hlt
  refine ⟨min r (cap ε),le_min hr.1 (cap_pos ht),?_,?_,?_⟩
  · exact (show ((min r (cap ε):ℕ):WithTop ℕ) ≤ r by exact_mod_cast min_le_left r (cap ε)).trans hr.2
  · exact (Nat.cast_le.mpr (min_le_right r (cap ε))).trans (orderTerm_zero_log_ceil hε ht).2
  · exact (truncate_score hβ hε hε1 ht r hr.1).trans
      ((mul_le_mul_of_nonneg_left hscore.le (Real.exp_pos _).le).trans_eq (by ring))

end Smoothness2601.UpperOrder
