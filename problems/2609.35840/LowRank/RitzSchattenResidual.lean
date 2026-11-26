import LowRank.SpectralCompressionPinching
import LowRank.RitzVariationalPower

/-! For p at least two, captured-power deficits give actual residual
guarantees. The Ritz-value hypotheses remain explicit; no convergence or
probability estimate is assumed to have been proved by these identities. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem schattenPower_eq_optimum_add_capture {a b k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) {p : ℝ} (hp : 0 < p) :
    schattenPower p A = optimalSchattenPower p A k +
      schattenPower p (A * optimalColumnSelector a b k hk A) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  let sp := canonicalOrderedSpectrum (m + k) (symmetricRightGram A)
  rw [optimalColumnSelector_schattenPower, schattenPower_eq_symmetricPowerTrace,
    symmetricPowerTrace_eq _ sp, optimalSchattenPower_eq_bottom_of_le hp A hk]
  simp only [Nat.add_sub_cancel, lastColumnIndex_add]
  unfold bottomPowerTrace
  rw [(orderedMatrixSpectrum (rightGram_posSemidef A).isHermitian).value_unique sp]
  exact Fin.sum_univ_add (fun i => sp.value i ^ (p / 2))

theorem schattenPower_column_residual_le_sub_capture {a b k : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (Z : Matrix (Fin b) (Fin k) ℝ) (hZ : Zᵀ * Z = 1)
    {p : ℝ} (hp : 2 ≤ p) :
    schattenPower p (A * (1 - Z * Zᵀ)) ≤ schattenPower p A - schattenPower p (A * Z) := by
  have h := schattenPower_projector_pinching hp A (column_projector Z hZ)
  rw [← Matrix.mul_assoc, schattenPower_right_extension (by linarith : 0 < p) _ Z hZ] at h
  linarith

theorem schattenNorm_relative_of_power_excess {a b k : ℕ} (hk : k ≤ b)
    (A B : Matrix (Fin a) (Fin b) ℝ) {p ε : ℝ} (hp : 1 ≤ p) (hε : 0 ≤ ε)
    (h : schattenPower p B ≤ (1 + ε) * optimalSchattenPower p A k) :
    schattenNorm p B ≤ (1 + ε) * optimalSchattenNorm p A k := by
  have hp0 : 0 < p := by linarith
  have hopt : 0 ≤ optimalSchattenPower p A k := by
    rw [← optimalColumnSelector_residual_power hk A hp0]
    exact schattenPower_nonneg _ _
  have hc : 0 ≤ 1 + ε := by linarith
  have hscale : 1 + ε ≤ (1 + ε) ^ p := Real.self_le_rpow_of_one_le (by linarith) hp
  have hpow := h.trans (mul_le_mul_of_nonneg_right hscale hopt)
  have hn := Real.rpow_le_rpow (schattenPower_nonneg p B) hpow (by positivity : 0 ≤ 1 / p)
  rw [Real.mul_rpow (Real.rpow_nonneg hc p) hopt, ← Real.rpow_mul hc,
    show p * (1 / p) = 1 by field_simp, Real.rpow_one] at hn
  exact hn

theorem schattenPower_residual_le_optimum_add_deficit {a b k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) (Z : Matrix (Fin b) (Fin k) ℝ) (hZ : Zᵀ * Z = 1)
    {p δ : ℝ} (hp : 2 ≤ p)
    (hcapture : schattenPower p (A * optimalColumnSelector a b k hk A) - δ ≤
      schattenPower p (A * Z)) :
    schattenPower p (A * (1 - Z * Zᵀ)) ≤ optimalSchattenPower p A k + δ := by
  have h := schattenPower_column_residual_le_sub_capture A Z hZ hp
  rw [schattenPower_eq_optimum_add_capture hk A (by linarith : 0 < p)] at h
  linarith

theorem compressedRitz_relative_of_ritz_errors {a b k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) {P : Matrix (Fin b) (Fin b) ℝ}
    (hP : IsOrthogonalProjector P) {p ε : ℝ} (hp : 2 ≤ p) (hε : 0 ≤ ε)
    (e : Fin k → ℝ) (he : ∀ j, 0 ≤ e j)
    (happrox : ∀ j, (canonicalOrderedSpectrum b (symmetricRightGram A)).value
      (lastColumnIndex b k hk j) - e j ≤
        (canonicalOrderedSpectrum b (symmetricRightGram (A * P))).value (lastColumnIndex b k hk j))
    (hbudget : (∑ j, max 1 (p / 2) * e j *
      ((canonicalOrderedSpectrum b (symmetricRightGram A)).value
        (lastColumnIndex b k hk j)) ^ (p / 2 - 1)) ≤ ε * optimalSchattenPower p A k) :
    let Z := optimalColumnSelector a b k hk (A * P)
    schattenNorm p (A * (1 - Z * Zᵀ)) ≤ (1 + ε) * optimalSchattenNorm p A k := by
  dsimp only
  have hc := compressedRitz_power_deficit_of_projector hk A hP (by linarith : 0 < p)
    (fun j => (canonicalOrderedSpectrum b (symmetricRightGram A)).value (lastColumnIndex b k hk j))
    e (fun j => (canonicalOrderedSpectrum b (symmetricRightGram A)).value_nonneg
      (rightGram_posSemidef A) (lastColumnIndex b k hk j)) he happrox
  rw [← optimalColumnSelector_schattenPower hk A p] at hc
  have hr := schattenPower_residual_le_optimum_add_deficit hk A _
    (optimalColumnSelector_orthogonal hk (A * P)) hp hc
  apply schattenNorm_relative_of_power_excess hk A _ (by linarith : 1 ≤ p) hε
  linarith

end
end LowRank
