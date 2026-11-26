import LowRank.SchattenRankBounded
import LowRank.ColumnRangeProjector

/-! Zero Schatten residual is exactly matrix equality. A matrix with k
columns generates a Gram input with zero optimal rank-k residual. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem frobeniusSq_eq_zero_iff {a b : Type*} [Fintype a] [Fintype b]
    (X : Matrix a b ℝ) : frobeniusSq X = 0 ↔ X = 0 := by
  constructor
  · intro h
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      Finset.sum_nonneg (fun j _ => sq_nonneg (X i j)))).mp h
    ext i j
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (X i j))).mp
      (hi i (Finset.mem_univ i)) j (Finset.mem_univ j)
    exact pow_eq_zero hj
  · rintro rfl
    simp [frobeniusSq]

theorem schattenPower_eq_zero_iff_singularValues {d t : ℕ} {p : ℝ} (hp : p ≠ 0)
    (X : Matrix (Fin d) (Fin t) ℝ) :
    schattenPower p X = 0 ↔ ∀ i, singularValue X i = 0 := by
  constructor
  · intro h i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      Real.rpow_nonneg (singularValue_nonneg X j) p)).mp h i (Finset.mem_univ i)
    exact (Real.rpow_eq_zero (singularValue_nonneg X i) hp).mp hi
  · intro h
    apply Finset.sum_eq_zero
    intro i _
    rw [h i, Real.zero_rpow hp]

theorem schattenPower_eq_zero_iff {d t : ℕ} {p : ℝ} (hp : p ≠ 0)
    (X : Matrix (Fin d) (Fin t) ℝ) : schattenPower p X = 0 ↔ X = 0 := by
  rw [schattenPower_eq_zero_iff_singularValues hp,
    ← schattenPower_eq_zero_iff_singularValues (by norm_num : (2 : ℝ) ≠ 0),
    schattenPower_two, frobeniusSq_eq_zero_iff]

theorem schattenNorm_eq_zero_iff {d t : ℕ} {p : ℝ} (hp : p ≠ 0)
    (X : Matrix (Fin d) (Fin t) ℝ) : schattenNorm p X = 0 ↔ X = 0 := by
  rw [schattenNorm, Real.rpow_eq_zero (schattenPower_nonneg p X) (one_div_ne_zero hp),
    schattenPower_eq_zero_iff hp]

theorem gram_columnRangeProjector_residual {d k : ℕ} (X : Matrix (Fin d) (Fin k) ℝ) :
    (X * Xᵀ) * (1 - columnRangeProjector X) = 0 := by
  have hleft : (1 - columnRangeProjector X) * X = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, columnRangeProjector_fixes, sub_self]
  have ht := congrArg Matrix.transpose hleft
  simp only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
    (columnRangeProjector_isProjector X).symmetric, Matrix.transpose_zero] at ht
  rw [Matrix.mul_assoc, ht, Matrix.mul_zero]

theorem optimalSchattenNorm_gram_eq_zero {d k : ℕ} {p : ℝ} (hp : 0 < p)
    (X : Matrix (Fin d) (Fin k) ℝ) (hk : k ≤ d) :
    optimalSchattenNorm p (X * Xᵀ) k = 0 := by
  have hleast := optimalSchattenNorm_isLeast_rankBounded hp (X * Xᵀ) hk
  apply le_antisymm
  · apply hleast.2
    refine ⟨columnRangeProjector X, columnRangeProjector_isProjector X,
      columnRangeProjector_rank_le X, ?_⟩
    rw [gram_columnRangeProjector_residual]
    exact ((schattenNorm_eq_zero_iff (ne_of_gt hp) _).mpr rfl).symm
  · obtain ⟨P, _, _, heq⟩ := hleast.1
    rw [heq]
    exact schattenNorm_nonneg _ _

theorem relative_gram_schatten_implies_exact {d k : ℕ} {p ε : ℝ} (hp : 0 < p)
    (X : Matrix (Fin d) (Fin k) ℝ) (hk : k ≤ d) (P : Matrix (Fin d) (Fin d) ℝ)
    (h : schattenNorm p ((X * Xᵀ) * (1 - P)) ≤
      (1 + ε) * optimalSchattenNorm p (X * Xᵀ) k) :
    (X * Xᵀ) * (1 - P) = 0 := by
  rw [optimalSchattenNorm_gram_eq_zero hp X hk, mul_zero] at h
  exact (schattenNorm_eq_zero_iff (ne_of_gt hp) _).mp
    (le_antisymm h (schattenNorm_nonneg _ _))

end
end LowRank
