import LowRank.GeneralPairedKrylovSuccess
import LowRank.GeneralKrylovRoundBounds

/-! An explicit query envelope for every finite Schatten exponent. -/

namespace LowRank
noncomputable section

def generalNarrowTolerance (p : ℝ) (a k : ℕ) (ε : ℝ) : ℝ :=
  confidentRitzTolerance (weightedNarrowError p ε) (40 * (k : ℝ)) (2 * k + 2) a

def generalWideTolerance (p : ℝ) (a k : ℕ) (ε : ℝ) : ℝ :=
  confidentRitzTolerance (weightedWideError p k ε) (40 * (k : ℝ)) (2 * generalWideKrylovRank p k ε + 2) a

def generalNarrowRounds (p : ℝ) (a k : ℕ) (ε : ℝ) : ℕ :=
  chebyshevFilterDegree (powerBoostedGap (weightedNarrowError p ε) (powerBoostOrder p))
    (generalNarrowTolerance p a k ε) + powerBoostOrder p + 1

def generalWideRounds (p : ℝ) (a k : ℕ) (ε : ℝ) : ℕ :=
  chebyshevFilterDegree 1 (generalWideTolerance p a k ε) + powerBoostOrder p + 1

def generalPairedQueryBudget (p : ℝ) (a k : ℕ) (ε : ℝ) : ℕ :=
  pairedKrylovQueryBudget (2 * k + 2) (2 * generalWideKrylovRank p k ε + 2)
    (generalNarrowRounds p a k ε) (generalWideRounds p a k ε)

def generalQueryLogFactor (p : ℝ) (a k : ℕ) (ε : ℝ) : ℝ :=
  8 * (2 * Real.log (2 / generalNarrowTolerance p a k ε) * powerBoostCost p + (powerBoostOrder p : ℝ) + 2) +
    (4 * (4 : ℝ) ^ (p / 2) + 12) *
      (2 * Real.log (2 / generalWideTolerance p a k ε) + (powerBoostOrder p : ℝ) + 2) +
        (4 : ℝ) ^ (p / 2) + 3

theorem generalNarrowTolerance_bounds {p ε : ℝ} {a k : ℕ}
    (hk : 0 < k) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 < generalNarrowTolerance p a k ε ∧ generalNarrowTolerance p a k ε ≤ 1 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  exact ⟨confidentRitzTolerance_pos (weightedNarrowError_pos hε) (by positivity) (by omega),
    confidentRitzTolerance_le_one (weightedNarrowError_le_one hε.le hε1) (by linarith) (by omega)⟩

theorem generalWideTolerance_bounds {p ε : ℝ} {a k : ℕ}
    (hk : 0 < k) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 < generalWideTolerance p a k ε ∧ generalWideTolerance p a k ε ≤ 1 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  exact ⟨confidentRitzTolerance_pos (weightedWideError_pos hk hε) (by positivity) (by omega),
    confidentRitzTolerance_le_one (weightedWideError_le_one hk hε1) (by linarith) (by omega)⟩

theorem generalQueryLogFactor_ge {p ε : ℝ} {a k : ℕ}
    (hk : 0 < k) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (4 : ℝ) ^ (p / 2) + 3 ≤ generalQueryLogFactor p a k ε := by
  obtain ⟨hN, hN1⟩ := generalNarrowTolerance_bounds (p := p) (a := a) hk hε hε1
  obtain ⟨hW, hW1⟩ := generalWideTolerance_bounds (p := p) (a := a) hk hε hε1
  have hlogN : 0 ≤ Real.log (2 / generalNarrowTolerance p a k ε) :=
    Real.log_nonneg ((le_div_iff₀ hN).mpr (by linarith))
  have hlogW : 0 ≤ Real.log (2 / generalWideTolerance p a k ε) :=
    Real.log_nonneg ((le_div_iff₀ hW).mpr (by linarith))
  have hC := (powerBoostCost_pos p).le
  unfold generalQueryLogFactor
  have hsum : 0 ≤ 8 * (2 * Real.log (2 / generalNarrowTolerance p a k ε) * powerBoostCost p +
      (powerBoostOrder p : ℝ) + 2) + (4 * (4 : ℝ) ^ (p / 2) + 12) *
      (2 * Real.log (2 / generalWideTolerance p a k ε) + (powerBoostOrder p : ℝ) + 2) := by positivity
  linarith

theorem generalPairedQueryBudget_add_rank_le {p ε : ℝ} {a k : ℕ}
    (hk : 0 < k) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((generalPairedQueryBudget p a k ε : ℝ) + k) ≤
      (k : ℝ) * accuracyScale ε * generalQueryLogFactor p a k ε := by
  obtain ⟨hN, hN1⟩ := generalNarrowTolerance_bounds (p := p) (a := a) hk hε hε1
  obtain ⟨hW, hW1⟩ := generalWideTolerance_bounds (p := p) (a := a) hk hε hε1
  have hn := weightedNarrowDegree_le (p := p) hε hε1 hN hN1
  have hr := weightedWideDegree_le (p := p) hW hW1
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hs : 2 * ((2 * k + 2 : ℕ) : ℝ) ≤ 8 * (k : ℝ) := by push_cast; linarith
  have ha := accuracyScale_pos hε
  have ht : 2 * ((2 * generalWideKrylovRank p k ε + 2 : ℕ) : ℝ) ≤
      (4 * (4 : ℝ) ^ (p / 2) + 12) * ((k : ℝ) * accuracyScale ε) := by
    have h := generalWideKrylovBlockWidth_le (p := p) hk hε hε1
    nlinarith
  have hleft := mul_le_mul hs hn (Nat.cast_nonneg _) (by positivity : 0 ≤ 8 * (k : ℝ))
  have hright := mul_le_mul ht hr (Nat.cast_nonneg _)
    (by positivity : 0 ≤ (4 * (4 : ℝ) ^ (p / 2) + 12) * ((k : ℝ) * accuracyScale ε))
  have hks : (k : ℝ) ≤ (k : ℝ) * accuracyScale ε :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) (accuracyScale_ge_one hε hε1)
  have hpow : 0 ≤ (4 : ℝ) ^ (p / 2) := Real.rpow_nonneg (by norm_num) _
  have hsp : 0 ≤ (k : ℝ) * accuracyScale ε := by positivity
  have hextra := mul_nonneg hsp hpow
  unfold generalPairedQueryBudget generalNarrowRounds generalWideRounds
  rw [pairedKrylovQueryBudget_eq]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hleft hright ⊢
  unfold generalQueryLogFactor
  nlinarith [add_le_add hleft hright]

end
end LowRank
