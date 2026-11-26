import LowRank.MatrixOrder

/-! Deterministic conversion of a matrix spectral gap and an energy bound into
overlap. These theorems use actual matrices and Loewner order. They do not prove
the Wishart spectral event or the Schatten compression theorem. -/

namespace LowRank
open Matrix
open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem spectral_gap_overlap_deficit {P K W : Matrix n n ℝ} {γ E k : ℝ}
    (hP : IsOrthogonalProjector P) (hγ : 0 < γ) (htr : P.trace = k)
    (hgap : LoewnerLE (γ • (1 - K)) W) (henergy : (P * W).trace ≤ E) :
    k - (P * K).trace ≤ E / γ := by
  have h := (trace_mul_mono hP.posSemidef hgap).trans henergy
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, mul_sub,
    mul_one, Matrix.trace_sub, htr] at h
  apply (le_div_iff₀ hγ).mpr
  nlinarith

theorem wishart_gap_overlap_deficit {P K W : Matrix n n ℝ} {c₀ C ε d k : ℝ}
    (hP : IsOrthogonalProjector P) (hc : 0 < c₀) (hk : 0 < k) (hd : 0 < d)
    (htr : P.trace = k)
    (hgap : LoewnerLE ((c₀ * (k / d) ^ 2) • (1 - K)) W)
    (henergy : (P * W).trace ≤ C * ε * d) :
    k - (P * K).trace ≤ (C / c₀) * ε * d ^ 3 / k ^ 2 := by
  have hγ : 0 < c₀ * (k / d) ^ 2 := mul_pos hc (sq_pos_of_pos (div_pos hk hd))
  have h := spectral_gap_overlap_deficit hP hγ htr hgap henergy
  convert h using 1 <;> field_simp <;> ring

/-- Cubic smallness is the exact condition used by the dimension choice. -/
theorem overlap_of_cubic_smallness {k z C ε d : ℝ}
    (hk : 0 < k) (hdeficit : k - z ≤ C * ε * d ^ 3 / k ^ 2)
    (hsmall : C * ε * d ^ 3 ≤ k ^ 3 / 4) : 3 * k / 4 ≤ z := by
  have hdiv : C * ε * d ^ 3 / k ^ 2 ≤ k / 4 := by
    apply (div_le_iff₀ (sq_pos_of_pos hk)).mpr
    nlinarith [hsmall]
  linarith

end LowRank
