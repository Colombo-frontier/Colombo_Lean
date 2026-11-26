import LowRank.HardSpectrumBridge

/-! General positive-p relative Schatten error forces overlap with the
Wishart nullspace on the specified deterministic spectral event. -/

namespace LowRank
open Matrix
open scoped Matrix
noncomputable section

theorem exists_schatten_hard_instance_overlap {p L c₀ : ℝ}
    (hp : 0 < p) (hL : 0 < L) (hc : 0 < c₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ {d k : ℕ} {ε : ℝ}
      {W P K : Matrix (Fin d) (Fin d) ℝ},
      k ≤ d → 0 < k → W.PosSemidef → IsOrthogonalProjector P → IsOrthogonalProjector K →
      P.rank = k → K.rank = k → K * W = 0 →
      LoewnerLE W ((L / 2) • 1) →
      LoewnerLE ((c₀ * ((k : ℝ) / (d : ℝ)) ^ 2) • (1 - K)) W →
      0 ≤ ε → ε ≤ 1 →
      schattenNorm p (hardMatrix L W * (1 - P)) ≤
        (1 + ε) * optimalSchattenNorm p (hardMatrix L W) k →
      (k : ℝ) - (P * K).trace ≤ C * ε * (d : ℝ) ^ 3 / (k : ℝ) ^ 2 := by
  obtain ⟨C, hC, hcompression⟩ := well_conditioned_relative_schatten_compression
    (a := (1 / 2 : ℝ)) (b := 1) (by norm_num) (by norm_num) hp
  refine ⟨((2 * L / 3) * C) / c₀, by positivity, ?_⟩
  intro d k ε W P K hkd
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkd
  intro hk hW hP hK hPrank hKrank hKW hbound hgap hε hε1 hsuccess
  have hsym : Wᵀ = W := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hW.isHermitian.eq
  have hH : (hardMatrix L W).IsHermitian := by
    simpa only [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] using
      hardMatrix_symmetric L hsym
  obtain ⟨hlow, hupp⟩ := hardMatrix_spectral_interval hL hW hbound
  have hcomp := hcompression (hardMatrix L W) hH hP hPrank hlow
    (by simpa only [one_smul] using hupp) hε hε1 hsuccess
  rw [hardMatrix_compression_deficit hL hW hK hKrank hKW hbound] at hcomp
  have htr : P.trace = (k : ℝ) := by rw [hP.trace_eq_rank, hPrank]
  have he := compression_deficit_to_energy hL hW hP htr hbound hcomp
  have he' : (P * W).trace ≤ ((2 * L / 3) * C) * ε * (k + m : ℕ) := by
    simpa only [mul_assoc] using he
  exact wishart_gap_overlap_deficit hP hc (by exact_mod_cast hk)
    (by exact_mod_cast (show 0 < k + m by omega)) htr hgap he'

end
end LowRank
