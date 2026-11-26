import LowRank.GeneralExplicitPolylog

/-! The manuscript's fixed finite-p minimax rate, with a concrete common
logarithmic factor and constants depending only on p. -/

namespace LowRank
open scoped ENNReal
noncomputable section
universe u

def rateLogarithm (N k : ℕ) (ε : ℝ) : ℝ :=
  1 + Real.log ((k : ℝ) ^ 2 * ((N : ℝ) + 1) / ε)

def rateLogScale (p : ℝ) : ℝ :=
  1024 * (2 * (4 : ℝ) ^ (p / 2) + 6) * max 1 (p / 2)

def rateLogCoefficient (p : ℝ) : ℝ := 16 * powerBoostCost p + 8 * (4 : ℝ) ^ (p / 2) + 24

def rateConstantTerm (p : ℝ) : ℝ :=
  (20 + 4 * (4 : ℝ) ^ (p / 2)) * ((powerBoostOrder p : ℝ) + 2) + (4 : ℝ) ^ (p / 2) + 3

def rateUpperConstant (p : ℝ) : ℝ :=
  rateLogCoefficient p * (1 + Real.log (rateLogScale p)) + rateConstantTerm p

theorem rateLogScale_ge_one (p : ℝ) : 1 ≤ rateLogScale p := by
  have hf : 0 ≤ (4 : ℝ) ^ (p / 2) := Real.rpow_nonneg (by norm_num) _
  have hM : 1 ≤ max 1 (p / 2) := le_max_left _ _
  have hmul := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ 1024 * (2 * (4 : ℝ) ^ (p / 2) + 6))
  unfold rateLogScale
  nlinarith

theorem rateLogCoefficient_pos (p : ℝ) : 0 < rateLogCoefficient p := by
  have hc := powerBoostCost_pos p
  unfold rateLogCoefficient
  positivity

theorem rateConstantTerm_pos (p : ℝ) : 0 < rateConstantTerm p := by
  unfold rateConstantTerm
  positivity

theorem rateUpperConstant_pos (p : ℝ) : 0 < rateUpperConstant p := by
  have hc := rateLogCoefficient_pos p
  have hb := rateConstantTerm_pos p
  have hd := Real.log_nonneg (rateLogScale_ge_one p)
  unfold rateUpperConstant
  positivity

theorem generalPolylog_le_common_log {p ε : ℝ} {N k : ℕ}
    (hk : 0 < k) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    generalPolylog p N k ε ≤ rateUpperConstant p * rateLogarithm N k ε := by
  let X := (k : ℝ) ^ 2 * ((N : ℝ) + 1) / ε
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hksq : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ hk1
  have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg N)
  have hX : 1 ≤ X := by
    apply (le_div_iff₀ hε).mpr
    have hn := one_le_mul_of_one_le_of_one_le hksq hN1
    linarith
  have hXp : 0 < X := by linarith
  have hD := rateLogScale_ge_one p
  have hDp : 0 < rateLogScale p := by linarith
  have harg : generalLogArgument p N k ε = rateLogScale p * X := by
    unfold generalLogArgument rateLogScale X
    ring
  have he : generalPolylog p N k ε =
      rateLogCoefficient p * Real.log X +
        (rateLogCoefficient p * Real.log (rateLogScale p) + rateConstantTerm p) := by
    unfold generalPolylog
    rw [harg, Real.log_mul hDp.ne' hXp.ne']
    unfold rateLogCoefficient rateConstantTerm
    ring
  have hlogX := Real.log_nonneg hX
  have hlogD := Real.log_nonneg hD
  have hα := (rateLogCoefficient_pos p).le
  have hβ := (rateConstantTerm_pos p).le
  have hβ' : 0 ≤ rateLogCoefficient p * Real.log (rateLogScale p) + rateConstantTerm p := by positivity
  have hcross := mul_nonneg hβ' hlogX
  rw [he]
  change _ ≤ rateUpperConstant p * (1 + Real.log X)
  unfold rateUpperConstant
  nlinarith

theorem fixed_schatten_minimax_rate {p : ℝ} (hp : 1 ≤ p) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (a b k : ℕ) (ε δ : ℝ),
      0 < k → k < min a b → 0 < ε → ε ≤ 1 → 1 / 5 ≤ δ → δ ≤ 19 / 20 →
      ENNReal.ofReal (c * targetRate (min a b) k ε) ≤ rectangularQueryComplexity.{u} a b k p ε δ ∧
      rectangularQueryComplexity.{u} a b k p ε δ ≤
        ENNReal.ofReal (C * targetRate (min a b) k ε * rateLogarithm (min a b) k ε) := by
  obtain ⟨c, hc, hmain⟩ := rectangularQueryComplexity_two_sided_general_explicit_polylog.{u} hp
  refine ⟨c, rateUpperConstant p, hc, rateUpperConstant_pos p, ?_⟩
  intro a b k ε δ hk hkN hε hε1 hδ hδ1
  obtain ⟨hlo, hup⟩ := hmain a b k ε δ hk hkN hε hε1 hδ hδ1
  refine ⟨hlo, hup.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hR : 0 ≤ targetRate (min a b) k ε :=
    le_min (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg k) (accuracyScale_pos hε).le)
  have h := mul_le_mul_of_nonneg_right (generalPolylog_le_common_log (p := p) (N := min a b) hk hε hε1) hR
  nlinarith

theorem fixed_schatten_minimax_two_thirds {p : ℝ} (hp : 1 ≤ p) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (a b k : ℕ) (ε : ℝ),
      0 < k → k < min a b → 0 < ε → ε ≤ 1 →
      ENNReal.ofReal (c * targetRate (min a b) k ε) ≤ rectangularQueryComplexity.{u} a b k p ε (2 / 3) ∧
      rectangularQueryComplexity.{u} a b k p ε (2 / 3) ≤
        ENNReal.ofReal (C * targetRate (min a b) k ε * rateLogarithm (min a b) k ε) := by
  obtain ⟨c, C, hc, hC, h⟩ := fixed_schatten_minimax_rate.{u} hp
  exact ⟨c, C, hc, hC, fun a b k ε hk hkN hε hε1 =>
    h a b k ε (2 / 3) hk hkN hε hε1 (by norm_num) (by norm_num)⟩

end
end LowRank
