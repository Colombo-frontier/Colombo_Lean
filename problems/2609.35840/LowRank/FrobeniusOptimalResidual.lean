import LowRank.FrobeniusHardInstance
import LowRank.ProjectorRank
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! The actual optimal squared Frobenius residual over rank-at-most-k
orthogonal projectors. Its value is measurable; on the hard spectral event
the Wishart kernel attains this minimum. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

def RankBoundedProjector (d k : ℕ) :=
  {P : Matrix (Fin d) (Fin d) ℝ // IsOrthogonalProjector P ∧ P.rank ≤ k}

instance rankBoundedProjector_nonempty (d k : ℕ) : Nonempty (RankBoundedProjector d k) :=
  ⟨⟨0, ⟨⟨by simp, by simp⟩, by simp⟩⟩⟩

def optimalFrobeniusSq {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ) (k : ℕ) : ℝ :=
  ⨅ P : RankBoundedProjector d k, frobeniusSq (H * (1 - P.1))

theorem frobenius_projector_errors_bddBelow {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ) (k : ℕ) :
    BddBelow (Set.range (fun P : RankBoundedProjector d k => frobeniusSq (H * (1 - P.1)))) :=
  ⟨0, fun _ ⟨_, hP⟩ => hP ▸ frobeniusSq_nonneg _⟩

theorem optimalFrobeniusSq_nonneg {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ) (k : ℕ) :
    0 ≤ optimalFrobeniusSq H k :=
  le_ciInf (fun _ => frobeniusSq_nonneg _)

theorem optimalFrobeniusSq_le {d k : ℕ} (H : Matrix (Fin d) (Fin d) ℝ)
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P) (hrank : P.rank ≤ k) :
    optimalFrobeniusSq H k ≤ frobeniusSq (H * (1 - P)) :=
  ciInf_le (frobenius_projector_errors_bddBelow H k) ⟨P, hP, hrank⟩

theorem continuous_frobeniusSq (d t : ℕ) :
    Continuous (frobeniusSq : Matrix (Fin d) (Fin t) ℝ → ℝ) := by
  unfold frobeniusSq
  fun_prop

theorem measurable_optimalFrobeniusSq (d k : ℕ) :
    Measurable (fun H : Matrix (Fin d) (Fin d) ℝ => optimalFrobeniusSq H k) := by
  apply UpperSemicontinuous.measurable
  apply upperSemicontinuous_ciInf (fun H => frobenius_projector_errors_bddBelow H k)
  intro P
  have hc : Continuous (fun H : Matrix (Fin d) (Fin d) ℝ => frobeniusSq (H * (1 - P.1))) := by
    unfold frobeniusSq
    simp only [Matrix.mul_apply]
    fun_prop
  exact hc.upperSemicontinuous

theorem frobenius_kernel_minimal {d k : ℕ} {H K P : Matrix (Fin d) (Fin d) ℝ}
    (hH : Hᵀ = H) (hK : IsOrthogonalProjector K) (hKrank : K.rank = k)
    (hKunit : K * (H * H) = K) (hbound : LoewnerLE (H * H) 1)
    (hP : IsOrthogonalProjector P) (hPrank : P.rank ≤ k) :
    frobeniusSq (H * (1 - K)) ≤ frobeniusSq (H * (1 - P)) := by
  rw [frobeniusSq_residual H K hH hK, frobeniusSq_residual H P hH hP, hKunit]
  have h := trace_mul_mono hP.posSemidef hbound
  rw [mul_one] at h
  have hp := hP.trace_le_of_rank_le hPrank
  rw [hK.trace_eq_rank, hKrank]
  linarith

theorem optimalFrobeniusSq_eq_kernel {d k : ℕ} {H K : Matrix (Fin d) (Fin d) ℝ}
    (hH : Hᵀ = H) (hK : IsOrthogonalProjector K) (hKrank : K.rank = k)
    (hKunit : K * (H * H) = K) (hbound : LoewnerLE (H * H) 1) :
    optimalFrobeniusSq H k = frobeniusSq (H * (1 - K)) := by
  apply le_antisymm (optimalFrobeniusSq_le H hK hKrank.le)
  exact le_ciInf (fun P => frobenius_kernel_minimal hH hK hKrank hKunit hbound P.2.1 P.2.2)

theorem hardMatrix_optimalFrobeniusSq {d k : ℕ} {L : ℝ} {W K : Matrix (Fin d) (Fin d) ℝ}
    (hL : 0 < L) (hW : W.PosSemidef) (hK : IsOrthogonalProjector K) (hKrank : K.rank = k)
    (hKW : K * W = 0) (hbound : LoewnerLE W ((L / 2) • 1)) :
    optimalFrobeniusSq (hardMatrix L W) k = frobeniusSq (hardMatrix L W * (1 - K)) := by
  have hsym : Wᵀ = W := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hW.isHermitian.eq
  exact optimalFrobeniusSq_eq_kernel (hardMatrix_symmetric L hsym) hK hKrank
    (hardMatrix_kernel_unit L hKW) (hardMatrix_square_le_one hL hW hbound)

end
end LowRank
