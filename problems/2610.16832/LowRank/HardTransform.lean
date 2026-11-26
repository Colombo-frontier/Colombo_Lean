import LowRank.GaussianModel
import LowRank.SpectralOverlap

/-! The spectral algebra for H = I - W/L, at the level of Loewner order. -/

namespace LowRank
open Matrix
open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem psd_square_le {W : Matrix n n ℝ} {c : ℝ}
    (hW : W.PosSemidef) (hbound : LoewnerLE W (c • (1 : Matrix n n ℝ))) :
    LoewnerLE (W * W) (c • W) := by
  have h := loewner_congruence hbound hW.sqrt
  have hs : hW.sqrtᵀ = hW.sqrt := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hW.posSemidef_sqrt.isHermitian.eq
  have hsq : hW.sqrt * W * hW.sqrt = W * W := by
    have general (S A : Matrix n n ℝ) (hS : S * S = A) : S * A * S = A * A := by
      rw [← hS]
      noncomm_ring
    exact general _ _ hW.sqrt_mul_self
  simpa only [hs, hsq, Matrix.mul_smul, Matrix.smul_mul,
    mul_one, hW.sqrt_mul_self] using h

theorem transform_defect_identity {d : ℕ} (L : ℝ)
    (W : Matrix (Fin d) (Fin d) ℝ) :
    1 - hardMatrix L W * hardMatrix L W =
      (2 * L⁻¹) • W - (L⁻¹ * L⁻¹) • (W * W) := by
  unfold hardMatrix
  simp only [sub_mul, mul_sub, one_mul, mul_one,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  module

theorem transform_defect_loewner {d : ℕ} {L : ℝ}
    (hL : 0 < L) {W : Matrix (Fin d) (Fin d) ℝ} (hW : W.PosSemidef)
    (hbound : LoewnerLE W ((L / 2) • (1 : Matrix (Fin d) (Fin d) ℝ))) :
    LoewnerLE ((3 / (2 * L)) • W) (1 - hardMatrix L W * hardMatrix L W) := by
  have hw2 := psd_square_le hW hbound
  have h := psd_smul hw2 (mul_nonneg (inv_nonneg.mpr hL.le) (inv_nonneg.mpr hL.le))
  change ((L⁻¹ * L⁻¹) • ((L / 2) • W - W * W)).PosSemidef at h
  change (1 - hardMatrix L W * hardMatrix L W - (3 / (2 * L)) • W).PosSemidef
  rw [transform_defect_identity]
  have hc : 2 * L⁻¹ - 3 / (2 * L) = (L⁻¹ * L⁻¹) * (L / 2) := by
    field_simp
    <;> ring
  convert h using 1
  rw [smul_sub, smul_smul, ← hc]
  module

/-- Converts a compression deficit bound into the energy estimate used in the draft. -/
theorem compression_deficit_to_energy {d : ℕ} {L E k : ℝ}
    (hL : 0 < L) {W P : Matrix (Fin d) (Fin d) ℝ}
    (hW : W.PosSemidef) (hP : IsOrthogonalProjector P) (htr : P.trace = k)
    (hbound : LoewnerLE W ((L / 2) • (1 : Matrix (Fin d) (Fin d) ℝ)))
    (hdeficit : k - (P * (hardMatrix L W * hardMatrix L W)).trace ≤ E) :
    (P * W).trace ≤ (2 * L / 3) * E := by
  have h := trace_mul_mono hP.posSemidef (transform_defect_loewner hL hW hbound)
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, mul_sub,
    mul_one, Matrix.trace_sub, htr] at h
  have he := h.trans hdeficit
  have hpos : 0 < 3 / (2 * L) := by positivity
  have hdiv := (le_div_iff₀ hpos).mpr (by simpa [mul_comm] using he)
  convert hdiv using 1 <;> field_simp <;> ring

end LowRank
