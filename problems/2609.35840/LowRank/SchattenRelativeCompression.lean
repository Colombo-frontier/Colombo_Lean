import LowRank.MatrixSchattenCompression
import LowRank.RelativePowerGrowth

/-! Relative Schatten error implies an O(εd) compression deficit, with a
constant uniform over all matrix dimensions and target ranks. -/

namespace LowRank
open Matrix
open scoped Matrix
noncomputable section

theorem schatten_relative_power_bound {d k m : ℕ} {p ε : ℝ} (hp : 0 < p) (hε : 0 ≤ ε)
    (H : Matrix (Fin d) (Fin (k + m)) ℝ) (P : Matrix (Fin (k + m)) (Fin (k + m)) ℝ)
    (hsuccess : schattenNorm p (H * (1 - P)) ≤ (1 + ε) * optimalSchattenNorm p H k) :
    schattenPower p (H * (1 - P)) ≤ (1 + ε) ^ p * optimalSchattenPower p H k := by
  have h := Real.rpow_le_rpow (schattenNorm_nonneg p _) hsuccess hp.le
  have hopt : 0 ≤ optimalSchattenNorm p H k :=
    Real.rpow_nonneg (optimalSchattenPower_nonneg hp H) _
  rwa [schattenNorm_rpow (ne_of_gt hp), Real.mul_rpow (by linarith) hopt,
    optimalSchattenNorm_rpow hp] at h

theorem exists_uniform_relative_schatten_compression {a b p : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {d k m : ℕ} (H : Matrix (Fin d) (Fin (k + m)) ℝ)
      {P : Matrix (Fin (k + m)) (Fin (k + m)) ℝ} {ε : ℝ},
      IsOrthogonalProjector P → P.rank = k →
      LoewnerLE (a • 1) (Hᵀ * H) → LoewnerLE (Hᵀ * H) (b • 1) →
      0 ≤ ε → ε ≤ 1 →
      schattenNorm p (H * (1 - P)) ≤ (1 + ε) * optimalSchattenNorm p H k →
      gramCompressionDeficit H k P ≤ C * ε * (k + m : ℕ) := by
  obtain ⟨c, hc, hcompression⟩ := exists_uniform_schatten_compression ha hab hp
  obtain ⟨M, hM, hgrowth⟩ := exists_relative_rpow_growth hp
  have hb : 0 < b := ha.trans_le hab
  refine ⟨M * b ^ (p / 2) / c, by positivity, ?_⟩
  intro d k m H P ε hP hrank hlow hupp hε hε1 hsuccess
  have hcomp := hcompression H hP hrank hlow hupp
  have hpow := schatten_relative_power_bound hp hε H P hsuccess
  have hopt0 := optimalSchattenPower_nonneg hp H
  have hopt := optimalSchattenPower_le_dimension hp H hb.le hupp
  have hexcess : c * gramCompressionDeficit H k P ≤
      ((1 + ε) ^ p - 1) * optimalSchattenPower p H k := by nlinarith
  have hfin : c * gramCompressionDeficit H k P ≤
      M * ε * ((k + m : ℕ) * b ^ (p / 2)) :=
    hexcess.trans ((mul_le_mul_of_nonneg_right (hgrowth ε hε hε1) hopt0).trans
      (mul_le_mul_of_nonneg_left hopt (mul_nonneg hM.le hε)))
  apply (mul_le_mul_left hc).mp
  calc
    _ ≤ M * ε * ((k + m : ℕ) * b ^ (p / 2)) := hfin
    _ = c * (M * b ^ (p / 2) / c * ε * (k + m : ℕ)) := by
      field_simp
      ring

end
end LowRank
