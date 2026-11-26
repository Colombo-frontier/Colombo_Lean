import LowRank.SchattenOptimalResidual

/-! A dimension-uniform Schatten compression inequality for actual residuals
and their attained optimum, assuming a positive fixed interval for HᵀH. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

def gramCompressionDeficit {d t : ℕ} (H : Matrix (Fin d) (Fin t) ℝ)
    (k : ℕ) (P : Matrix (Fin t) (Fin t) ℝ) : ℝ :=
  (Hᵀ * H).trace - bottomPowerTrace (rightGram_posSemidef H).isHermitian
    (t - k) (Nat.sub_le t k) 1 - (P * (Hᵀ * H)).trace

theorem gramCompressionDeficit_eq_compressed_trace {d k m : ℕ}
    (H : Matrix (Fin d) (Fin (k + m)) ℝ) {P : Matrix (Fin (k + m)) (Fin (k + m)) ℝ}
    (B : Matrix (Fin (k + m)) (Fin m) ℝ) (hQ : B * Bᵀ = 1 - P) :
    gramCompressionDeficit H k P = (Bᵀ * (Hᵀ * H) * B).trace -
      bottomPowerTrace (rightGram_posSemidef H).isHermitian m (by omega) 1 := by
  simpa only [gramCompressionDeficit, Nat.add_sub_cancel_left] using
    (compression_trace_deficit B hQ
      (bottomPowerTrace (rightGram_posSemidef H).isHermitian m (by omega) 1)).symm

theorem gramCompressionDeficit_nonneg {d k m : ℕ}
    (H : Matrix (Fin d) (Fin (k + m)) ℝ) {P : Matrix (Fin (k + m)) (Fin (k + m)) ℝ}
    (hP : IsOrthogonalProjector P) (hrank : P.rank = k) : 0 ≤ gramCompressionDeficit H k P := by
  obtain ⟨B, hB, hQ⟩ := projector_complement_basis hP hrank
  rw [gramCompressionDeficit_eq_compressed_trace H B hQ]
  have h := compression_power_ge_bottom (show m ≤ k + m by omega) (rightGram_posSemidef H)
    B hB (show (0 : ℝ) ≤ 1 by norm_num)
  rw [symmetricPowerTrace_one] at h
  exact sub_nonneg.mpr h

theorem exists_uniform_schatten_compression {a b p : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hp : 0 < p) :
    ∃ c : ℝ, 0 < c ∧ ∀ {d k m : ℕ} (H : Matrix (Fin d) (Fin (k + m)) ℝ)
      {P : Matrix (Fin (k + m)) (Fin (k + m)) ℝ},
      IsOrthogonalProjector P → P.rank = k →
      LoewnerLE (a • 1) (Hᵀ * H) → LoewnerLE (Hᵀ * H) (b • 1) →
      c * gramCompressionDeficit H k P ≤
        schattenPower p (H * (1 - P)) - optimalSchattenPower p H k := by
  obtain ⟨c, hc, hbound⟩ := exists_uniform_compression_power_slope ha hab
    (show 0 < p / 2 by positivity)
  refine ⟨c, hc, ?_⟩
  intro d k m H P hP hrank hlow hupp
  obtain ⟨B, hB, hQ⟩ := projector_complement_basis hP hrank
  rw [gramCompressionDeficit_eq_compressed_trace H B hQ,
    schattenPower_residual_eq_compression hp H B hB hQ, optimalSchattenPower_eq_bottom hp H]
  exact hbound (by omega) (rightGram_posSemidef H).isHermitian B hB hlow hupp

theorem optimalSchattenPower_le_dimension {d k m : ℕ} {p b : ℝ} (hp : 0 < p)
    (H : Matrix (Fin d) (Fin (k + m)) ℝ) (hb : 0 ≤ b)
    (hbound : LoewnerLE (Hᵀ * H) (b • 1)) :
    optimalSchattenPower p H k ≤ (k + m : ℕ) * b ^ (p / 2) := by
  rw [optimalSchattenPower_eq_bottom hp H]
  have hlow : LoewnerLE ((0 : ℝ) • 1) (Hᵀ * H) := by
    simpa only [LoewnerLE, zero_smul, sub_zero] using rightGram_posSemidef H
  have hi (i : Fin m) : (orderedMatrixSpectrum (rightGram_posSemidef H).isHermitian).value
      (i.castLE (show m ≤ k + m by omega)) ^ (p / 2) ≤ b ^ (p / 2) :=
    Real.rpow_le_rpow ((orderedMatrixSpectrum (rightGram_posSemidef H).isHermitian).value_nonneg
      (rightGram_posSemidef H) _) ((orderedMatrixSpectrum
        (rightGram_posSemidef H).isHermitian).value_mem_Icc hlow hbound _).2 (by positivity)
  calc
    _ ≤ ∑ _ : Fin m, b ^ (p / 2) := Finset.sum_le_sum (fun i _ => hi i)
    _ = (m : ℝ) * b ^ (p / 2) := by simp
    _ ≤ (k + m : ℕ) * b ^ (p / 2) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast (show m ≤ k + m by omega))
        (Real.rpow_nonneg hb _)

end
end LowRank
