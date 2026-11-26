import LowRank.CubicPairedKrylovSuccess

/-! An explicit logarithmic multiplier for the paired query budget. -/

namespace LowRank
open Matrix
open scoped Matrix
noncomputable section

def cubicNarrowTolerance (a k : ℕ) (ε : ℝ) : ℝ :=
  confidentRitzTolerance (cubicKrylovGap ε) (40 * (k : ℝ)) (2 * k + 2) a

def cubicWideTolerance (a k : ℕ) (ε : ℝ) : ℝ :=
  confidentRitzTolerance (ε / (k : ℝ)) (40 * (k : ℝ)) (2 * wideKrylovRank k ε + 2) a

def cubicPairedQueryBudget (a k : ℕ) (ε : ℝ) : ℕ :=
  pairedKrylovQueryBudget (2 * k + 2) (2 * wideKrylovRank k ε + 2)
    (chebyshevFilterDegree (cubicKrylovGap ε) (cubicNarrowTolerance a k ε) + 1)
    (chebyshevFilterDegree 1 (cubicWideTolerance a k ε) + 1)

def cubicQueryLogFactor (a k : ℕ) (ε : ℝ) : ℝ :=
  8 * (2 * Real.log (2 / cubicNarrowTolerance a k ε) + 2) +
    28 * (2 * Real.log (2 / cubicWideTolerance a k ε) + 2)

theorem cubicNarrowTolerance_bounds {a k : ℕ} {ε : ℝ}
    (hk : 0 < k) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 < cubicNarrowTolerance a k ε ∧ cubicNarrowTolerance a k ε ≤ 1 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  exact ⟨confidentRitzTolerance_pos (cubicKrylovGap_pos hε) (by positivity) (by omega),
    confidentRitzTolerance_le_one (cubicKrylovGap_le_one hε.le hε1) (by linarith) (by omega)⟩

theorem cubicWideTolerance_bounds {a k : ℕ} {ε : ℝ}
    (hk : 0 < k) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 < cubicWideTolerance a k ε ∧ cubicWideTolerance a k ε ≤ 1 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkR : 0 < (k : ℝ) := by linarith
  exact ⟨confidentRitzTolerance_pos (div_pos hε hkR) (by positivity) (by omega),
    confidentRitzTolerance_le_one ((div_le_one hkR).mpr (hε1.trans hk1)) (by linarith) (by omega)⟩

theorem cubicQueryLogFactor_ge {a k : ℕ} {ε : ℝ}
    (hk : 0 < k) (hε : 0 < ε) (hε1 : ε ≤ 1) : 72 ≤ cubicQueryLogFactor a k ε := by
  obtain ⟨hN, hN1⟩ := cubicNarrowTolerance_bounds (a := a) hk hε hε1
  obtain ⟨hW, hW1⟩ := cubicWideTolerance_bounds (a := a) hk hε hε1
  have hlogN : 0 ≤ Real.log (2 / cubicNarrowTolerance a k ε) := Real.log_nonneg ((le_div_iff₀ hN).mpr (by linarith))
  have hlogW : 0 ≤ Real.log (2 / cubicWideTolerance a k ε) := Real.log_nonneg ((le_div_iff₀ hW).mpr (by linarith))
  unfold cubicQueryLogFactor
  linarith

theorem cubicPairedQueryBudget_le {a k : ℕ} {ε : ℝ}
    (hk : 0 < k) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (cubicPairedQueryBudget a k ε : ℝ) ≤
      (k : ℝ) * accuracyScale ε * cubicQueryLogFactor a k ε := by
  obtain ⟨hN, hN1⟩ := cubicNarrowTolerance_bounds (a := a) hk hε hε1
  obtain ⟨hW, hW1⟩ := cubicWideTolerance_bounds (a := a) hk hε hε1
  have hlogN : 0 ≤ Real.log (2 / cubicNarrowTolerance a k ε) := Real.log_nonneg ((le_div_iff₀ hN).mpr (by linarith))
  have hlogW : 0 ≤ Real.log (2 / cubicWideTolerance a k ε) := Real.log_nonneg ((le_div_iff₀ hW).mpr (by linarith))
  have hNdeg := chebyshevFilterDegree_le (cubicKrylovGap_pos hε) hN hN1
  rw [sqrt_cubicKrylovGap hε, div_inv_eq_mul] at hNdeg
  have hWdeg := chebyshevFilterDegree_le (by norm_num : (0 : ℝ) < 1) hW hW1
  norm_num only [Real.sqrt_one, div_one] at hWdeg
  have ha := accuracyScale_ge_one hε hε1
  have hn : ((chebyshevFilterDegree (cubicKrylovGap ε) (cubicNarrowTolerance a k ε) + 1 : ℕ) : ℝ) ≤
      (2 * Real.log (2 / cubicNarrowTolerance a k ε) + 2) * accuracyScale ε := by
    push_cast
    nlinarith
  have hr : ((chebyshevFilterDegree 1 (cubicWideTolerance a k ε) + 1 : ℕ) : ℝ) ≤
      2 * Real.log (2 / cubicWideTolerance a k ε) + 2 := by
    push_cast
    linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hs : 2 * ((2 * k + 2 : ℕ) : ℝ) ≤ 8 * (k : ℝ) := by push_cast; linarith
  have ht : 2 * ((2 * wideKrylovRank k ε + 2 : ℕ) : ℝ) ≤ 28 * ((k : ℝ) * accuracyScale ε) := by
    have h := wideKrylovBlockWidth_le hk hε hε1
    linarith
  have hleft := mul_le_mul hs hn (Nat.cast_nonneg _) (by positivity : 0 ≤ 8 * (k : ℝ))
  have hright := mul_le_mul ht hr (Nat.cast_nonneg _)
    (by positivity : 0 ≤ 28 * ((k : ℝ) * accuracyScale ε))
  unfold cubicPairedQueryBudget
  rw [pairedKrylovQueryBudget_eq]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hleft hright ⊢
  unfold cubicQueryLogFactor
  nlinarith [add_le_add hleft hright]

end
end LowRank
