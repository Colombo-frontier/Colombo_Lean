import Smoothness2601.OrderTradeoff

noncomputable section
namespace Smoothness2601

def phaseCoefficient (β : ℝ) : ℝ := (Real.exp β / β ^ β)^2

theorem phaseCoefficient_pos {β : ℝ} (hβ : 0 < β) : 0 < phaseCoefficient β :=
  sq_pos_of_pos (div_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hβ _))

theorem phase_rate_identity {β t : ℝ} (hβ : 0 < β) (ht : 0 ≤ t) :
    ((t/β)^β*Real.exp β)^2 = phaseCoefficient β*t^(2*β) := by
  rw [Real.div_rpow ht hβ.le,mul_pow,div_pow]
  have ht2 : (t^β)^2 = t^(2*β) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul ht]
    congr 1
    ring
  rw [ht2]
  unfold phaseCoefficient
  rw [div_pow]
  ring

theorem orderTerm_rate_identity {p : ℕ} (hp : 1 ≤ p) {β ε : ℝ} (hε : 0 < ε) :
    ε^(-4:ℝ)*orderTerm β ε p ^ 2 = (p:ℝ)^(2*β)*ε^(-4-2/(p:ℝ)) := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hp)
  rw [orderTerm,mul_pow]
  have hp2 : ((p:ℝ)^β)^2 = (p:ℝ)^(2*β) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hp0.le]
    congr 1
    ring
  have he2 : (ε^(-1/(p:ℝ)))^2 = ε^(-2/(p:ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hε.le]
    congr 1
    ring
  rw [hp2,he2,mul_left_comm,← Real.rpow_add hε]
  congr 2
  ring

end Smoothness2601
