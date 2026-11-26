import LowRank.WideTailPower

/-! Integer block sizes for the small-tail branch, with an explicit
cubic-root query envelope and no unquantified dimension rounding. -/

namespace LowRank
open Matrix
open scoped Matrix
noncomputable section
universe u

def wideKrylovRank (k : ℕ) (ε : ℝ) : ℕ := k + ⌈4 * (k : ℝ) * accuracyScale ε⌉₊

theorem accuracyScale_ge_one {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) : 1 ≤ accuracyScale ε := by
  simpa only [accuracyScale, Real.one_rpow] using
    Real.rpow_le_rpow_of_nonpos hε hε1 (by norm_num : -(1 : ℝ) / 3 ≤ 0)

theorem wideKrylovRank_ge (k : ℕ) (ε : ℝ) : k ≤ wideKrylovRank k ε := Nat.le_add_right _ _

theorem wideKrylovRank_surplus (k : ℕ) (ε : ℝ) :
    4 * ((k : ℝ) * accuracyScale ε) ≤ ((wideKrylovRank k ε - k : ℕ) : ℝ) := by
  simp only [wideKrylovRank, Nat.add_sub_cancel_left]
  simpa only [mul_assoc] using Nat.le_ceil (4 * (k : ℝ) * accuracyScale ε)

theorem wideKrylovRank_le {k : ℕ} {ε : ℝ} (hk : 0 < k) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (wideKrylovRank k ε : ℝ) ≤ 6 * ((k : ℝ) * accuracyScale ε) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ha := accuracyScale_ge_one hε hε1
  have hka : (k : ℝ) ≤ (k : ℝ) * accuracyScale ε := le_mul_of_one_le_right (by positivity) ha
  have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ 4 * (k : ℝ) * accuracyScale ε)
  simp only [wideKrylovRank, Nat.cast_add]
  nlinarith

theorem wideKrylovBlockWidth_le {k : ℕ} {ε : ℝ} (hk : 0 < k) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((2 * wideKrylovRank k ε + 2 : ℕ) : ℝ) ≤ 14 * ((k : ℝ) * accuracyScale ε) := by
  have h := wideKrylovRank_le hk hε hε1
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ha := accuracyScale_ge_one hε hε1
  have hka : (1 : ℝ) ≤ (k : ℝ) * accuracyScale ε := one_le_mul_of_one_le_of_one_le hk1 ha
  push_cast
  linarith

theorem refinedKrylovAlgorithm_wide_cubic_query_count {a b k : ℕ}
    (hk0 : 0 < k) (hka : k ≤ a) (hkb : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let s := 2 * wideKrylovRank k ε + 2
    let η := confidentRitzTolerance (ε / (k : ℝ)) (40 * (k : ℝ)) s a
    let n := chebyshevFilterDegree 1 η + 1
    ∀ seed : (refinedKrylovAlgorithm.{u} a b k s n hka hkb).Seed,
      (((refinedKrylovAlgorithm.{u} a b k s n hka hkb).policy.toProgram a b
        (krylovQueryBudget s 0 n) seed).calls (rectangularOracle A) : ℝ) ≤
          28 * ((k : ℝ) * accuracyScale ε) * (2 * Real.log (2 / η) + 2) := by
  dsimp only
  intro seed
  have hs : 0 < 2 * wideKrylovRank k ε + 2 := by omega
  have h := refinedKrylovAlgorithm_wide_query_count hk0 hka hkb hs A hε hε1 seed
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk0
  have hkpos : 0 < (k : ℝ) := by linarith
  have hη := confidentRitzTolerance_pos (d := a) (div_pos hε hkpos)
    (by positivity : 0 < 40 * (k : ℝ)) hs
  have hη1 := confidentRitzTolerance_le_one (d := a)
    ((div_le_one hkpos).mpr (hε1.trans hkR)) (by linarith : 1 ≤ 40 * (k : ℝ)) hs
  have hlog : 0 ≤ Real.log (2 / confidentRitzTolerance (ε / (k : ℝ)) (40 * (k : ℝ))
      (2 * wideKrylovRank k ε + 2) a) :=
    Real.log_nonneg ((le_div_iff₀ hη).mpr (by linarith))
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (by linarith : 0 ≤ 2 * Real.log
    (2 / confidentRitzTolerance (ε / (k : ℝ)) (40 * (k : ℝ)) (2 * wideKrylovRank k ε + 2) a) + 2)
  have hw := wideKrylovBlockWidth_le hk0 hε hε1
  nlinarith

end
end LowRank
