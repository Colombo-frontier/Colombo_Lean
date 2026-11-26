import Smoothness2601.WeightGrowth

/-! One width constant controls every derivative order simultaneously. All
constants precede the order cap, including the infinite-order case. -/
noncomputable section
namespace Smoothness2601

theorem pow_rpow_comm_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (β : ℝ) :
    (x^n)^β = (x^β)^n := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hx,mul_comm,Real.rpow_mul hx,Real.rpow_natCast]

theorem factorial_sine_power {β K : ℝ} (hβ : 0 ≤ β) (hK : 0 < K) (k : ℕ) :
    ((k:ℝ)^β/K)^k ≤ (Real.exp 1^β/K)^k*(k.factorial:ℝ)^β := by
  have he : 0 < Real.exp 1^β := Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hbase : 0 ≤ (k:ℝ)/Real.exp 1 := div_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hf := Real.rpow_le_rpow (pow_nonneg hbase k) (factorial_lower_pow k) hβ
  rw [pow_rpow_comm_nonneg hbase,Real.div_rpow (Nat.cast_nonneg _) (Real.exp_pos _).le,div_pow] at hf
  have hp := (div_le_iff₀ (pow_pos he k)).mp hf
  rw [div_pow,div_pow]
  exact (div_le_div_of_nonneg_right hp (pow_nonneg hK.le k)).trans_eq (by ring)

theorem uniform_power_envelope {C M Λ β K : ℝ} (hC : 0 ≤ C) (hM : 0 < M)
    (hΛ : 0 < Λ) (hβ : 0 ≤ β) (hK : 0 < K)
    (ht : Real.exp 1^β/(K*Λ) ≤ 1)
    (hscale : C*(Real.exp 1^β/(K*Λ)) ≤ M*Λ)
    {k : ℕ} (hk : 1 ≤ k) :
    C*((k:ℝ)^β/K)^k ≤ M*Λ^(k+1)*((k+1).factorial:ℝ)^β := by
  let t := Real.exp 1^β/(K*Λ)
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have htk : t^k ≤ t := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [pow_add,pow_one]
    exact (mul_le_mul_of_nonneg_left (pow_le_one₀ ht0 ht) ht0).trans_eq (mul_one _)
  have hc : C*t^k ≤ M*Λ := (mul_le_mul_of_nonneg_left htk hC).trans hscale
  have hf : (k.factorial:ℝ)^β ≤ ((k+1).factorial:ℝ)^β :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.factorial_le (Nat.le_succ k)) hβ
  have he : C*(Real.exp 1^β/K)^k*(k.factorial:ℝ)^β =
      (C*t^k)*Λ^k*(k.factorial:ℝ)^β := by
    dsimp [t]
    simp only [div_pow,mul_pow]
    field_simp
    ring
  calc
    _ ≤ C*((Real.exp 1^β/K)^k*(k.factorial:ℝ)^β) :=
      mul_le_mul_of_nonneg_left (factorial_sine_power hβ hK k) hC
    _ = (C*t^k)*Λ^k*(k.factorial:ℝ)^β := by rw [← he]; ring
    _ ≤ (M*Λ)*Λ^k*((k+1).factorial:ℝ)^β :=
      mul_le_mul (mul_le_mul_of_nonneg_right hc (pow_nonneg hΛ.le k)) hf
        (by positivity) (by positivity)
    _ = _ := by rw [pow_succ]; ring

theorem sineWidth_uniform_envelope {p : WithTop ℕ} {C M Λ β K s : ℝ}
    (hp : 1 ≤ p) (hC : 0 ≤ C) (hM : 0 < M) (hΛ : 0 < Λ) (hβ : 0 ≤ β)
    (hK : 0 < K) (hs : 0 < s) (hs1 : s ≤ 1)
    (ht : Real.exp 1^β/(K*Λ) ≤ 1)
    (hscale : C*(Real.exp 1^β/(K*Λ)) ≤ M*Λ)
    {k : ℕ} (hk : k ∈ availableOrders p) :
    C*s*(sineWidth p β s K)⁻¹^k ≤ M*Λ^(k+1)*((k+1).factorial:ℝ)^β := by
  have hb := mul_le_mul_of_nonneg_left
    (sineWidth_derivative_budget hp hβ hs hs1 hK hk) hC
  calc
    _ = C*(s*(sineWidth p β s K)⁻¹^k) := by ring
    _ ≤ C*((k:ℝ)^β/K)^k := hb
    _ ≤ _ := uniform_power_envelope hC hM hΛ hβ hK ht hscale hk.1

end Smoothness2601
