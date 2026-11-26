import FullJet.Scaling
import FullJet.ChainSmoothness

namespace FullJet

noncomputable def scaleConstant (p : ℕ) : ℝ := chainDerivativeBound (p + 1) + 1

theorem scaleConstant_pos (p : ℕ) : 0 < scaleConstant p := by
  have h := chainDerivativeBound_nonneg (p + 1)
  dsimp [scaleConstant]
  linarith

noncomputable def chainBeta (p : ℕ) (L ρ ε : ℝ) : ℝ :=
  (L * ρ / (32 * scaleConstant p * ε)) ^ (1 / (p : ℝ))

noncomputable def chainAlpha (p : ℕ) (L ρ ε : ℝ) : ℝ := 32 * ε / chainBeta p L ρ ε

theorem chainBeta_pos (p : ℕ) (L ρ ε : ℝ) (hL : 0 < L) (hρ : 0 < ρ) (hε : 0 < ε) :
    0 < chainBeta p L ρ ε := Real.rpow_pos_of_pos
      (div_pos (mul_pos hL hρ) (mul_pos (mul_pos (by norm_num) (scaleConstant_pos p)) hε)) _

theorem chainAlpha_pos (p : ℕ) (L ρ ε : ℝ) (hL : 0 < L) (hρ : 0 < ρ) (hε : 0 < ε) :
    0 < chainAlpha p L ρ ε := div_pos (by positivity) (chainBeta_pos p L ρ ε hL hρ hε)

theorem chainBeta_pow (p : ℕ) (hp : 0 < p) (L ρ ε : ℝ)
    (hL : 0 < L) (hρ : 0 < ρ) (hε : 0 < ε) :
    chainBeta p L ρ ε ^ p = L * ρ / (32 * scaleConstant p * ε) := by
  have hb : 0 ≤ L * ρ / (32 * scaleConstant p * ε) := by
    have := scaleConstant_pos p
    positivity
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [chainBeta, ← Real.rpow_natCast, ← Real.rpow_mul hb, one_div_mul_cancel hp', Real.rpow_one]

theorem chainAlpha_beta (p : ℕ) (L ρ ε : ℝ) (hL : 0 < L) (hρ : 0 < ρ) (hε : 0 < ε) :
    chainAlpha p L ρ ε * chainBeta p L ρ ε / 4 = 8 * ε := by
  have hb := chainBeta_pos p L ρ ε hL hρ hε
  unfold chainAlpha
  rw [div_mul_cancel₀ _ hb.ne']
  ring

theorem chain_parameters_smooth (p : ℕ) (hp : 0 < p) (L ρ ε : ℝ)
    (hL : 0 < L) (hρ : 0 < ρ) (hε : 0 < ε) :
    chainAlpha p L ρ ε * chainBeta p L ρ ε ^ (p + 1) *
      (chainDerivativeBound (p + 1) / ρ) ≤ L := by
  have hb := chainBeta_pos p L ρ ε hL hρ hε
  have hH := scaleConstant_pos p
  have hidentity : chainAlpha p L ρ ε * chainBeta p L ρ ε ^ (p + 1) *
      (scaleConstant p / ρ) = L := by
    rw [chainAlpha, pow_succ, chainBeta_pow p hp L ρ ε hL hρ hε]
    field_simp
    <;> ring
  apply LE.le.trans ?_ hidentity.le
  apply mul_le_mul_of_nonneg_left
  · apply div_le_div_of_nonneg_right _ hρ.le
    dsimp [scaleConstant]
    linarith
  · exact mul_nonneg (chainAlpha_pos p L ρ ε hL hρ hε).le (pow_nonneg hb.le _)

noncomputable def chainStageCapacity (p : ℕ) (Δ L ρ ε : ℝ) : ℝ :=
  Δ / (2 * chainAlpha p L ρ ε)

theorem chainStageCapacity_pos (p : ℕ) (Δ L ρ ε : ℝ)
    (hΔ : 0 < Δ) (hL : 0 < L) (hρ : 0 < ρ) (hε : 0 < ε) :
    0 < chainStageCapacity p Δ L ρ ε :=
  div_pos hΔ (mul_pos (by norm_num) (chainAlpha_pos p L ρ ε hL hρ hε))

theorem chain_parameters_gap (p T : ℕ) (Δ L ρ ε : ℝ)
    (hL : 0 < L) (hρ : 0 < ρ) (hε : 0 < ε)
    (hT : (T + 1 : ℕ) ≤ chainStageCapacity p Δ L ρ ε) :
    chainAlpha p L ρ ε * (2 * (T + 1 : ℕ)) ≤ Δ := by
  have hh := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2)
    (chainAlpha_pos p L ρ ε hL hρ hε))).mp hT
  nlinarith only [hh]

end FullJet
