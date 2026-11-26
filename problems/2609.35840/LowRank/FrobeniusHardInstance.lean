import LowRank.FrobeniusCompression

/-! Actual p=2 residual error forces nullspace overlap on the specified spectral
event. The probability of this event and the posterior query bound are separate. -/

namespace LowRank
open Matrix
open scoped Matrix

theorem hardMatrix_square_le_one {d : ℕ} {L : ℝ}
    (hL : 0 < L) {W : Matrix (Fin d) (Fin d) ℝ} (hW : W.PosSemidef)
    (hbound : LoewnerLE W ((L / 2) • (1 : Matrix (Fin d) (Fin d) ℝ))) :
    LoewnerLE (hardMatrix L W * hardMatrix L W) 1 := by
  have h := (transform_defect_loewner hL hW hbound).add
    (psd_smul hW (show 0 ≤ 3 / (2 * L) by positivity))
  simpa only [LoewnerLE, sub_add_cancel] using h

theorem hardMatrix_kernel_unit {d : ℕ} (L : ℝ)
    {W K : Matrix (Fin d) (Fin d) ℝ} (hKW : K * W = 0) :
    K * (hardMatrix L W * hardMatrix L W) = K := by
  have hKH : K * hardMatrix L W = K := by
    simp only [hardMatrix, mul_sub, mul_one, Matrix.mul_smul, hKW, smul_zero, sub_zero]
  rw [← mul_assoc, hKH, hKH]

theorem frobenius_hard_instance_overlap {d : ℕ} {L c₀ k ε : ℝ}
    {W P K : Matrix (Fin d) (Fin d) ℝ}
    (hL : 0 < L) (hc : 0 < c₀) (hk : 0 < k) (hd : 0 < (d : ℝ))
    (hW : W.PosSemidef) (hP : IsOrthogonalProjector P) (hK : IsOrthogonalProjector K)
    (hPtr : P.trace = k) (hKtr : K.trace = k) (hKW : K * W = 0)
    (hbound : LoewnerLE W ((L / 2) • (1 : Matrix (Fin d) (Fin d) ℝ)))
    (hgap : LoewnerLE ((c₀ * (k / d) ^ 2) • (1 - K)) W)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hrelative : frobeniusSq (hardMatrix L W * (1 - P)) ≤
      (1 + ε) ^ 2 * frobeniusSq (hardMatrix L W * (1 - K))) :
    k - (P * K).trace ≤ (2 * L / c₀) * ε * (d : ℝ) ^ 3 / k ^ 2 := by
  have hsym : Wᵀ = W := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hW.isHermitian.eq
  have hcomp := frobenius_relative_compression (hardMatrix_symmetric L hsym) hP hK hKtr
    (hardMatrix_kernel_unit L hKW) (hardMatrix_square_le_one hL hW hbound) hε hε1 hrelative
  simp only [Fintype.card_fin] at hcomp
  have he := compression_deficit_to_energy hL hW hP hPtr hbound hcomp
  have he' : (P * W).trace ≤ (2 * L) * ε * d := by nlinarith only [he]
  exact wishart_gap_overlap_deficit hP hc hk hd hPtr hgap he'

end LowRank
