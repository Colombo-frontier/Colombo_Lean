import LowRank.TailPowerBudget
import LowRank.RateArithmetic

/-! The large-tail regime attains the cubic-root accuracy dependence for
1 <= p <= 2. The complementary regime is handled by WideTailPower. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section
universe u

def cubicKrylovGap (ε : ℝ) : ℝ := ε ^ ((2 : ℝ) / 3)

theorem cubicKrylovGap_pos {ε : ℝ} (hε : 0 < ε) : 0 < cubicKrylovGap ε :=
  Real.rpow_pos_of_pos hε _

theorem cubicKrylovGap_le_one {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) : cubicKrylovGap ε ≤ 1 :=
  Real.rpow_le_one hε hε1 (by norm_num)

theorem cubicKrylovGap_eq_mul_scale {ε : ℝ} (hε : 0 < ε) :
    cubicKrylovGap ε = ε * accuracyScale ε := by
  unfold cubicKrylovGap accuracyScale
  conv_rhs => lhs; rw [← Real.rpow_one ε]
  rw [← Real.rpow_add hε]
  norm_num

theorem sqrt_cubicKrylovGap {ε : ℝ} (hε : 0 < ε) :
    Real.sqrt (cubicKrylovGap ε) = (accuracyScale ε)⁻¹ := by
  rw [cubicKrylovGap, Real.sqrt_eq_rpow, ← Real.rpow_mul hε.le]
  unfold accuracyScale
  rw [← Real.rpow_neg hε.le]
  norm_num

theorem confidentRitzTolerance_le_one {γ q : ℝ} {s d : ℕ}
    (hγ : γ ≤ 1) (hq : 1 ≤ q) (hs : 0 < s) : confidentRitzTolerance γ q s d ≤ 1 := by
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hq1 : (1 : ℝ) ≤ q ^ 2 := one_le_pow₀ hq
  have hd1 : (1 : ℝ) ≤ (d : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg d)
  have hqs : (1 : ℝ) ≤ q ^ 2 * (s : ℝ) := one_le_mul_of_one_le_of_one_le hq1 hs1
  have hprod : (1 : ℝ) ≤ q ^ 2 * (s : ℝ) * ((d : ℝ) + 1) :=
    one_le_mul_of_one_le_of_one_le hqs hd1
  have hd : 0 < 2 * q ^ 2 * (s : ℝ) * ((d : ℝ) + 1) := by positivity
  rw [confidentRitzTolerance, Real.sqrt_le_one]
  apply (div_le_one hd).mpr
  nlinarith

theorem refinedKrylovAlgorithm_large_tail_success {b m k s n : ℕ}
    (hm : 0 < m) (hk0 : 0 < k) (hkb : k ≤ b)
    (A : Matrix (Fin (m + k)) (Fin b) ℝ) (hs : 2 * k + 2 ≤ s)
    {p ε : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hn : chebyshevFilterDegree (cubicKrylovGap ε)
      (confidentRitzTolerance (cubicKrylovGap ε) (40 * (k : ℝ)) s (m + k)) < n)
    (hlarge : (k : ℝ) * accuracyScale ε *
      ((canonicalOrderedSpectrum (m + k) (symmetricRightGram Aᵀ)).value
        (⟨m - 1, by omega⟩ : Fin (m + k))) ^ (p / 2) ≤ optimalSchattenPower p A k) :
    19 / 20 ≤ (refinedKrylovAlgorithm.{u} (m + k) b k s n (by omega) hkb).law.real
      (rectangularSchattenSuccess p ε
        (refinedKrylovAlgorithm.{u} (m + k) b k s n (by omega) hkb).policy A) := by
  apply refinedKrylovAlgorithm_tail_success_of_budget hm hk0 hkb A hs hp hp2
    (cubicKrylovGap_pos hε) (cubicKrylovGap_le_one hε.le hε1) hε.le hn
  let L := (canonicalOrderedSpectrum (m + k) (symmetricRightGram Aᵀ)).value
    (⟨m - 1, by omega⟩ : Fin (m + k))
  have hL : 0 ≤ L := (canonicalOrderedSpectrum (m + k) (symmetricRightGram Aᵀ)).value_nonneg
    (rightGram_posSemidef Aᵀ) _
  have hpL : 0 ≤ L ^ (p / 2) := Real.rpow_nonneg hL _
  calc
    _ ≤ (k : ℝ) * cubicKrylovGap ε * L ^ (p / 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (by linarith [cubicKrylovGap_pos hε] : cubicKrylovGap ε / 2 ≤ cubicKrylovGap ε)
        (Nat.cast_nonneg k)) hpL
    _ = ε * ((k : ℝ) * accuracyScale ε * L ^ (p / 2)) := by
      rw [cubicKrylovGap_eq_mul_scale hε]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlarge hε.le

theorem refinedKrylovAlgorithm_cubic_query_count {a b k s : ℕ}
    (hk0 : 0 < k) (hka : k ≤ a) (hkb : k ≤ b) (hs : 0 < s)
    (A : Matrix (Fin a) (Fin b) ℝ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let η := confidentRitzTolerance (cubicKrylovGap ε) (40 * (k : ℝ)) s a
    let n := chebyshevFilterDegree (cubicKrylovGap ε) η + 1
    ∀ seed : (refinedKrylovAlgorithm.{u} a b k s n hka hkb).Seed,
      (((refinedKrylovAlgorithm.{u} a b k s n hka hkb).policy.toProgram a b
        (krylovQueryBudget s 0 n) seed).calls (rectangularOracle A) : ℝ) ≤
          2 * (s : ℝ) * (2 * Real.log (2 / η) * accuracyScale ε + 2) := by
  dsimp only
  intro seed
  rw [refinedKrylovAlgorithm_calls]
  push_cast
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk0
  have hη := confidentRitzTolerance_pos (d := a) (cubicKrylovGap_pos hε)
    (by positivity : 0 < 40 * (k : ℝ)) hs
  have hη1 := confidentRitzTolerance_le_one (d := a) (cubicKrylovGap_le_one hε.le hε1)
    (by linarith : 1 ≤ 40 * (k : ℝ)) hs
  have h := chebyshevFilterDegree_le (cubicKrylovGap_pos hε) hη hη1
  rw [sqrt_cubicKrylovGap hε, div_inv_eq_mul] at h
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2 * (s : ℝ))
  linarith

end
end LowRank
