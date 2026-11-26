import LowRank.SchattenTruncation
import LowRank.SchattenRankBounded

/-! Isometric embeddings, including zero padding, preserve the best rank-k
Schatten residual. Truncating a column output therefore preserves a relative
error guarantee as well as its rank upper bound. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem isometric_projector {b t : ℕ}
    (R : Matrix (Fin b) (Fin t) ℝ) (hR : Rᵀ * R = 1)
    {P : Matrix (Fin t) (Fin t) ℝ} (hP : IsOrthogonalProjector P) :
    IsOrthogonalProjector (R * P * Rᵀ) := by
  constructor
  · simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hP.symmetric, Matrix.mul_assoc]
  · calc
      _ = R * P * (Rᵀ * R) * P * Rᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hR, Matrix.mul_one, Matrix.mul_assoc R P P, hP.idempotent]

theorem isometric_projector_rank_le {b t : ℕ}
    (R : Matrix (Fin b) (Fin t) ℝ) (P : Matrix (Fin t) (Fin t) ℝ) :
    (R * P * Rᵀ).rank ≤ P.rank :=
  (Matrix.rank_mul_le_left (R * P) Rᵀ).trans (Matrix.rank_mul_le_right R P)

theorem isometric_residual_factorization {a b d t : ℕ}
    (L : Matrix (Fin a) (Fin d) ℝ)
    (R : Matrix (Fin b) (Fin t) ℝ) (hR : Rᵀ * R = 1)
    (A : Matrix (Fin d) (Fin t) ℝ) (P : Matrix (Fin t) (Fin t) ℝ) :
    L * A * Rᵀ * (1 - R * P * Rᵀ) = L * (A * (1 - P)) * Rᵀ := by
  calc
    _ = L * A * Rᵀ - L * A * (Rᵀ * R) * P * Rᵀ := by
      simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
    _ = L * A * Rᵀ - L * A * P * Rᵀ := by rw [hR, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]

theorem optimalSchattenPower_isometric_embedding {a b d t k : ℕ} {p : ℝ} (hp : 0 < p)
    (L : Matrix (Fin a) (Fin d) ℝ) (hL : Lᵀ * L = 1)
    (R : Matrix (Fin b) (Fin t) ℝ) (hR : Rᵀ * R = 1)
    (A : Matrix (Fin d) (Fin t) ℝ) (hk : k ≤ t) :
    optimalSchattenPower p (L * A * Rᵀ) k = optimalSchattenPower p A k := by
  have hkb : k ≤ b := hk.trans (orthogonal_columns_dimension_le R hR)
  apply le_antisymm
  · obtain ⟨P, hP, hrank, heq⟩ := (optimalSchattenPower_isLeast_rankBounded hp A hk).1
    calc
      _ ≤ schattenPower p (L * A * Rᵀ * (1 - R * P * Rᵀ)) :=
        optimalSchattenPower_le_rankBounded hp _ hkb (isometric_projector R hR hP)
          ((isometric_projector_rank_le R P).trans hrank)
      _ = schattenPower p (A * (1 - P)) := by
        rw [isometric_residual_factorization L R hR A P,
          schattenPower_isometric_embedding hp L hL R hR]
      _ = _ := heq.symm
  · obtain ⟨Q, hQ, hrank, heq⟩ :=
      (optimalSchattenPower_isLeast_rankBounded hp (L * A * Rᵀ) hkb).1
    obtain ⟨Z, _, hZQ⟩ := projector_basis_factorization hQ rfl
    obtain ⟨hP, hPk, hs⟩ := truncatedColumnProjector_spec R Z
    calc
      _ ≤ schattenPower p (A * (1 - truncatedColumnProjector R Z)) :=
        optimalSchattenPower_le_rankBounded hp A hk hP (hPk.trans hrank)
      _ ≤ schattenPower p (L * A * Rᵀ * (1 - Z * Zᵀ)) :=
        schattenPower_truncated_residual_le hp L hL R hR A Z hP hs
      _ = _ := by rw [hZQ, ← heq]

theorem optimalSchattenNorm_isometric_embedding {a b d t k : ℕ} {p : ℝ} (hp : 0 < p)
    (L : Matrix (Fin a) (Fin d) ℝ) (hL : Lᵀ * L = 1)
    (R : Matrix (Fin b) (Fin t) ℝ) (hR : Rᵀ * R = 1)
    (A : Matrix (Fin d) (Fin t) ℝ) (hk : k ≤ t) :
    optimalSchattenNorm p (L * A * Rᵀ) k = optimalSchattenNorm p A k := by
  simp only [optimalSchattenNorm, optimalSchattenPower_isometric_embedding hp L hL R hR A hk]

theorem relative_schatten_truncation {a b d t k : ℕ} {p ε : ℝ} (hp : 0 < p)
    (L : Matrix (Fin a) (Fin d) ℝ) (hL : Lᵀ * L = 1)
    (R : Matrix (Fin b) (Fin t) ℝ) (hR : Rᵀ * R = 1)
    (A : Matrix (Fin d) (Fin t) ℝ) (hk : k ≤ t) (Z : Matrix (Fin b) (Fin k) ℝ)
    (hsuccess : schattenNorm p (L * A * Rᵀ * (1 - Z * Zᵀ)) ≤
      (1 + ε) * optimalSchattenNorm p (L * A * Rᵀ) k) :
    IsOrthogonalProjector (truncatedColumnProjector R Z) ∧
      (truncatedColumnProjector R Z).rank ≤ k ∧
      schattenNorm p (A * (1 - truncatedColumnProjector R Z)) ≤
        (1 + ε) * optimalSchattenNorm p A k := by
  obtain ⟨hP, hrank, _⟩ := truncatedColumnProjector_spec R Z
  refine ⟨hP, hrank, ?_⟩
  have h := (schattenNorm_truncatedColumnProjector_le hp L hL R hR A Z).trans hsuccess
  simpa only [optimalSchattenNorm_isometric_embedding hp L hL R hR A hk] using h

end
end LowRank
