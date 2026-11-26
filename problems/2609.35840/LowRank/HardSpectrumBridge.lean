import LowRank.WellConditionedSchatten
import LowRank.FrobeniusOptimalResidual

/-! Identify the general spectral compression deficit on the hard instance,
using the attained quadratic minimum to identify its top spectral trace. -/

namespace LowRank
open Matrix
open scoped Matrix
noncomputable section

theorem optimalSchattenPower_two_eq_kernel {k m : ℕ}
    {H K : Matrix (Fin (k + m)) (Fin (k + m)) ℝ}
    (hH : Hᵀ = H) (hK : IsOrthogonalProjector K) (hrank : K.rank = k)
    (hunit : K * (H * H) = K) (hbound : LoewnerLE (H * H) 1) :
    optimalSchattenPower 2 H k = frobeniusSq (H * (1 - K)) := by
  have hmin := optimalSchattenPower_isLeast (p := 2) (by norm_num) H
  apply le_antisymm
  · simpa only [schattenPower_two] using hmin.2 ⟨K, hK, hrank, rfl⟩
  · obtain ⟨P, hP, hPrank, heq⟩ := hmin.1
    rw [heq, schattenPower_two]
    exact frobenius_kernel_minimal hH hK hrank hunit hbound hP hPrank.le

theorem gramCompressionDeficit_eq_unit_kernel {k m : ℕ}
    {H K : Matrix (Fin (k + m)) (Fin (k + m)) ℝ}
    (hH : Hᵀ = H) (hK : IsOrthogonalProjector K) (hrank : K.rank = k)
    (hunit : K * (H * H) = K) (hbound : LoewnerLE (H * H) 1)
    (P : Matrix (Fin (k + m)) (Fin (k + m)) ℝ) :
    gramCompressionDeficit H k P = (k : ℝ) - (P * (H * H)).trace := by
  have hbottom : bottomPowerTrace (rightGram_posSemidef H).isHermitian m (by omega) 1 =
      frobeniusSq (H * (1 - K)) := by
    have h := (optimalSchattenPower_eq_bottom (p := 2) (by norm_num) H).symm.trans
      (optimalSchattenPower_two_eq_kernel hH hK hrank hunit hbound)
    simpa only [show (2 : ℝ) / 2 = 1 by norm_num] using h
  unfold gramCompressionDeficit
  simp only [Nat.add_sub_cancel_left]
  rw [hbottom, hH, frobeniusSq_residual H K hH hK, hunit, hK.trace_eq_rank, hrank]
  ring

theorem hardMatrix_spectral_interval {d : ℕ} {L : ℝ}
    {W : Matrix (Fin d) (Fin d) ℝ} (hL : 0 < L) (hW : W.PosSemidef)
    (hbound : LoewnerLE W ((L / 2) • 1)) :
    LoewnerLE ((1 / 2 : ℝ) • 1) (hardMatrix L W) ∧ LoewnerLE (hardMatrix L W) 1 := by
  constructor
  · have h := psd_smul hbound (inv_nonneg.mpr hL.le)
    change (hardMatrix L W - (1 / 2 : ℝ) • 1).PosSemidef
    convert h using 1
    change 1 - L⁻¹ • W - (1 / 2 : ℝ) • 1 = L⁻¹ • ((L / 2) • 1 - W)
    rw [smul_sub, smul_smul]
    have heq : L⁻¹ * (L / 2) = (1 / 2 : ℝ) := by field_simp
    rw [heq]
    module
  · simpa only [LoewnerLE, hardMatrix, sub_sub_cancel] using
      psd_smul hW (inv_nonneg.mpr hL.le)

theorem hardMatrix_compression_deficit {k m : ℕ} {L : ℝ}
    {W K : Matrix (Fin (k + m)) (Fin (k + m)) ℝ}
    (hL : 0 < L) (hW : W.PosSemidef) (hK : IsOrthogonalProjector K) (hrank : K.rank = k)
    (hKW : K * W = 0) (hbound : LoewnerLE W ((L / 2) • 1))
    (P : Matrix (Fin (k + m)) (Fin (k + m)) ℝ) :
    gramCompressionDeficit (hardMatrix L W) k P =
      (k : ℝ) - (P * (hardMatrix L W * hardMatrix L W)).trace := by
  have hsym : Wᵀ = W := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hW.isHermitian.eq
  exact gramCompressionDeficit_eq_unit_kernel (hardMatrix_symmetric L hsym) hK hrank
    (hardMatrix_kernel_unit L hKW) (hardMatrix_square_le_one hL hW hbound) P

end
end LowRank
