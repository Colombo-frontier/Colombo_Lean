import LowRank.FiniteZeroPadding
import LowRank.MeasurableProjectorCompletion

/-! The zero-padding output reduction with exactly rank-k output. Both
truncation and completion are measurable functions of the returned columns;
neither function receives the unknown input matrix. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators
noncomputable section

def completedTruncatedProjector {b t k : ℕ}
    (R : Matrix (Fin b) (Fin t) ℝ) (Z : Matrix (Fin b) (Fin k) ℝ) :
    Matrix (Fin t) (Fin t) ℝ := completeProjector k (truncatedColumnProjector R Z)

theorem completedTruncatedProjector_spec {b t k : ℕ} (hk : k ≤ t)
    (R : Matrix (Fin b) (Fin t) ℝ) (Z : Matrix (Fin b) (Fin k) ℝ) :
    IsOrthogonalProjector (completedTruncatedProjector R Z) ∧
      (completedTruncatedProjector R Z).rank = k ∧
      completedTruncatedProjector R Z * (Rᵀ * Z) = Rᵀ * Z := by
  obtain ⟨hP, hPk, hs⟩ := truncatedColumnProjector_spec R Z
  obtain ⟨hQ, hQk, hQP⟩ := completeProjector_spec hk hP hPk
  refine ⟨hQ, hQk, ?_⟩
  calc
    _ = completedTruncatedProjector R Z * (truncatedColumnProjector R Z * (Rᵀ * Z)) := by rw [hs]
    _ = Rᵀ * Z := by rw [← Matrix.mul_assoc, completedTruncatedProjector, hQP, hs]

theorem measurable_completedTruncatedProjector {b t k : ℕ}
    (R : Matrix (Fin b) (Fin t) ℝ) :
    Measurable (completedTruncatedProjector R : Matrix (Fin b) (Fin k) ℝ →
      Matrix (Fin t) (Fin t) ℝ) :=
  (measurable_completeProjector t k).comp (measurable_truncatedColumnProjector R)

theorem schattenNorm_completedTruncatedProjector_le {a b d t k : ℕ}
    (hk : k ≤ t) {p : ℝ} (hp : 0 < p)
    (L : Matrix (Fin a) (Fin d) ℝ) (hL : Lᵀ * L = 1)
    (R : Matrix (Fin b) (Fin t) ℝ) (hR : Rᵀ * R = 1)
    (A : Matrix (Fin d) (Fin t) ℝ) (Z : Matrix (Fin b) (Fin k) ℝ) :
    schattenNorm p (A * (1 - completedTruncatedProjector R Z)) ≤
      schattenNorm p (L * A * Rᵀ * (1 - Z * Zᵀ)) := by
  obtain ⟨hP, _, hs⟩ := completedTruncatedProjector_spec hk R Z
  exact Real.rpow_le_rpow (schattenPower_nonneg _ _)
    (schattenPower_truncated_residual_le hp L hL R hR A Z hP hs) (by positivity)

theorem completed_relative_schatten_truncation {a b d t k : ℕ}
    (hk : k ≤ t) {p ε : ℝ} (hp : 0 < p)
    (L : Matrix (Fin a) (Fin d) ℝ) (hL : Lᵀ * L = 1)
    (R : Matrix (Fin b) (Fin t) ℝ) (hR : Rᵀ * R = 1)
    (A : Matrix (Fin d) (Fin t) ℝ) (Z : Matrix (Fin b) (Fin k) ℝ)
    (hsuccess : schattenNorm p (L * A * Rᵀ * (1 - Z * Zᵀ)) ≤
      (1 + ε) * optimalSchattenNorm p (L * A * Rᵀ) k) :
    IsOrthogonalProjector (completedTruncatedProjector R Z) ∧
      (completedTruncatedProjector R Z).rank = k ∧
      schattenNorm p (A * (1 - completedTruncatedProjector R Z)) ≤
        (1 + ε) * optimalSchattenNorm p A k := by
  obtain ⟨hP, hrank, _⟩ := completedTruncatedProjector_spec hk R Z
  refine ⟨hP, hrank, ?_⟩
  have h := (schattenNorm_completedTruncatedProjector_le hk hp L hL R hR A Z).trans hsuccess
  simpa only [optimalSchattenNorm_isometric_embedding hp L hL R hR A hk] using h

theorem zeroPadFin_completed_relative_guarantee {a b d t k : ℕ}
    (hm : d ≤ a) (hn : t ≤ b) (A : Matrix (Fin d) (Fin t) ℝ) (hk : k ≤ t)
    {p ε : ℝ} (hp : 0 < p) (Z : Matrix (Fin b) (Fin k) ℝ)
    (hsuccess : schattenNorm p (zeroPadFin hm hn A * (1 - Z * Zᵀ)) ≤
      (1 + ε) * optimalSchattenNorm p (zeroPadFin hm hn A) k) :
    IsOrthogonalProjector (completedTruncatedProjector (coordinateEmbedding hn) Z) ∧
      (completedTruncatedProjector (coordinateEmbedding hn) Z).rank = k ∧
      schattenNorm p (A * (1 - completedTruncatedProjector (coordinateEmbedding hn) Z)) ≤
        (1 + ε) * optimalSchattenNorm p A k :=
  completed_relative_schatten_truncation hk hp _ (coordinateEmbedding_orthogonal hm)
    _ (coordinateEmbedding_orthogonal hn) A Z hsuccess

end
end LowRank
