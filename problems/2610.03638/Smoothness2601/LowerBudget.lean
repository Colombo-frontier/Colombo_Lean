import Smoothness2601.OrderTradeoff
import Smoothness2601.BernoulliOracle

/-! Integer chain length and the uniform fixed-budget algebra. No probability
or hardness conclusion is assumed by these arithmetic bridges. -/
noncomputable section
namespace Smoothness2601.LowerBudget

theorem integer_chain {A s : ℝ} (hs : 0 < s) (hsize : 2*s^2 ≤ A) :
    ∃ n : ℕ, A/(2*s^2) ≤ (n+1:ℝ) ∧ (n+1:ℝ) ≤ A/s^2 := by
  have hs2 := sq_pos_of_pos hs
  have ha : 2 ≤ A/s^2 := (le_div_iff₀ hs2).mpr hsize
  have ha0 : 0 ≤ A/s^2 := by linarith
  have hlo := Nat.floor_le ha0
  have hhi := Nat.lt_floor_add_one (A/s^2)
  have hfloor : 1 ≤ Nat.floor (A/s^2) := by
    have hf : (1:ℝ) ≤ Nat.floor (A/s^2) := by linarith
    exact_mod_cast hf
  obtain ⟨n,hn⟩ := Nat.exists_eq_add_of_le hfloor
  refine ⟨n,?_,?_⟩
  · rw [hn] at hhi
    push_cast at hhi
    have he : A/(2*s^2) = (A/s^2)/2 := by ring
    rw [he]
    linarith
  · rw [hn] at hlo
    push_cast at hlo
    linarith

theorem initial_gap {Δ τ C s : ℝ} {n : ℕ}
    (_hΔ : 0 < Δ) (hτ : 0 < τ) (hC : 0 ≤ C) (hs : 0 < s)
    (hT : (n+1:ℝ) ≤ (Δ*τ/(C+1))/s^2) :
    (s^2/τ)*(C*(n+1)+1/2) ≤ Δ := by
  have hN : (1:ℝ) ≤ n+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hc : C*(n+1)+1/2 ≤ (C+1)*(n+1) := by nlinarith
  have hb := mul_le_mul_of_nonneg_left hT (by positivity : 0 ≤ (s^2/τ)*(C+1))
  have he : (s^2/τ)*(C+1)*((Δ*τ/(C+1))/s^2) = Δ := by field_simp; ring
  rw [he] at hb
  exact (mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ s^2/τ)).trans (by
    convert hb using 1; ring)

theorem budget_reveal_bound {p : WithTop ℕ} {β s A C K σ : ℝ} {N T : ℕ}
    (hp : 1 ≤ p) (hβ : 0 ≤ β) (hs : 0 < s) (hs1 : s ≤ 1)
    (_hA : 0 ≤ A) (hC : 0 < C) (hK : 0 < K) (hσ : 0 < σ)
    (hT : A/(2*s^2) ≤ (T:ℝ))
    (hN : (N:ℝ) ≤ (A*σ^2/(16*C^2*K^2))*(orderTradeoff p β s)^2/s^4) :
    (N:ℝ)*BernoulliOracle.revealProbability (C*s*sineWidth p β s K) σ ≤ (T:ℝ)/8 := by
  have hD : 0 < orderTradeoff p β s := zero_lt_one.trans_le (orderTradeoff_one_le hp hβ hs hs1)
  have hq : 0 ≤ BernoulliOracle.revealProbability (C*s*sineWidth p β s K) σ := by
    unfold BernoulliOracle.revealProbability
    positivity
  have hh := mul_le_mul_of_nonneg_right hN hq
  have he : ((A*σ^2/(16*C^2*K^2))*(orderTradeoff p β s)^2/s^4)*
      BernoulliOracle.revealProbability (C*s*sineWidth p β s K) σ = A/(16*s^2) := by
    unfold BernoulliOracle.revealProbability sineWidth
    field_simp
    ring
  rw [he] at hh
  have ht : A/(16*s^2) ≤ (T:ℝ)/8 := by
    rw [show A/(16*s^2) = (A/(2*s^2))/8 by ring]
    exact div_le_div_of_nonneg_right hT (by norm_num)
  exact hh.trans ht

theorem accuracy_scale_rate {p : WithTop ℕ} {β ε a : ℝ}
    (hp : 1 ≤ p) (hβ : 0 ≤ β) (hε : 0 < ε) (ha : 1 ≤ a) (haε : a*ε ≤ 1) :
    (orderTradeoff p β ε)^2/(a^6*ε^4) ≤
      (orderTradeoff p β (a*ε))^2/(a*ε)^4 := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have he1 : ε ≤ 1 := by nlinarith
  have hD : 0 ≤ orderTradeoff p β ε := zero_le_one.trans (orderTradeoff_one_le hp hβ hε he1)
  have hD' : 0 ≤ orderTradeoff p β (a*ε) :=
    zero_le_one.trans (orderTradeoff_one_le hp hβ (mul_pos ha0 hε) haε)
  have hb := (orderTradeoff_scale (β := β) hp hε ha).1
  have hsq : (a⁻¹*orderTradeoff p β ε)^2 ≤ (orderTradeoff p β (a*ε))^2 :=
    (sq_le_sq₀ (mul_nonneg (inv_nonneg.mpr ha0.le) hD) hD').mpr hb
  have hm := div_le_div_of_nonneg_right hsq (pow_nonneg (mul_nonneg ha0.le hε.le) 4)
  have heq : (orderTradeoff p β ε)^2/(a^6*ε^4) =
      (a⁻¹*orderTradeoff p β ε)^2/(a*ε)^4 := by
    field_simp [ha0.ne',hε.ne']
    all_goals ring_nf
    all_goals simp
  rw [heq]
  exact hm

end Smoothness2601.LowerBudget
