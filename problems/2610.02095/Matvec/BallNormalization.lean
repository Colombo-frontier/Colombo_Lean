import Matvec.GameAlgebra
import Matvec.BallReduction
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Actual row normalization of the homogeneous ball embedding

For the manuscript's parameters, every row of `ballMatrix` and its negative
has Euclidean squared norm at most `5/16 < 1`. The proof uses the elementary
inequality `(a ± b)² ≤ 2a² + 2b²`, so the constant is deliberately loose.
The hypotheses are actual source-row sum-of-squares bounds and a unit-ball
right-hand side. No admissibility conclusion is assumed.
-/

namespace Matvec
namespace BallNormalization

open Matrix

theorem parameter_bounds {d : ℕ} (hd : 1 ≤ d) {κ α β : ℝ}
    (hκ : 1 ≤ κ) (hβ : β = 1 / (4 * κ)) (hα : α = β / (8 * Real.sqrt d)) :
    0 ≤ β ∧ β ≤ 1 / 4 ∧ β * κ = 1 / 4 ∧ 0 ≤ α ∧ α ≤ β := by
  have hk : 0 < κ := by linarith
  have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsqrt : (1 : ℝ) ≤ Real.sqrt d := by
    simpa using Real.sqrt_le_sqrt hdreal
  have hbp : 0 < β := by rw [hβ]; positivity
  have hprod : β * κ = 1 / 4 := by rw [hβ]; field_simp; ring
  have hbupper : β ≤ 1 / 4 := by nlinarith
  have hap : 0 ≤ α := by rw [hα]; positivity
  have haupper : α ≤ β := by
    rw [hα]
    apply (div_le_iff₀ (by positivity : 0 < 8 * Real.sqrt (d : ℝ))).2
    nlinarith
  exact ⟨hbp.le, hbupper, hprod, hap, haupper⟩

/-- Both signs of the homogeneous last coordinate obey the same bound. -/
theorem row_square_bound {κ α β B t : ℝ}
    (hβ : 0 ≤ β) (hβupper : β ≤ 1 / 4) (hprod : β * κ = 1 / 4)
    (hα : 0 ≤ α) (hαupper : α ≤ β) (hB : B ≤ κ ^ 2) (ht : t ^ 2 ≤ 1) :
    β ^ 2 * B + (α - β * t) ^ 2 ≤ 5 / 16 ∧
      β ^ 2 * B + (α + β * t) ^ 2 ≤ 5 / 16 := by
  have hfirst : β ^ 2 * B ≤ β ^ 2 * κ ^ 2 :=
    mul_le_mul_of_nonneg_left hB (sq_nonneg β)
  have hproduct : β ^ 2 * κ ^ 2 = 1 / 16 := by
    calc β ^ 2 * κ ^ 2 = (β * κ) ^ 2 := by ring
         _ = 1 / 16 := by rw [hprod]; norm_num
  have halpha : α ^ 2 ≤ β ^ 2 := by nlinarith
  have hbeta : β ^ 2 ≤ 1 / 16 := by nlinarith
  have hlast : (β * t) ^ 2 ≤ β ^ 2 := by
    have := mul_le_mul_of_nonneg_left ht (sq_nonneg β)
    nlinarith
  constructor
  · nlinarith [sq_nonneg (α + β * t)]
  · nlinarith [sq_nonneg (α - β * t)]

theorem ballMatrix_inl_row_sq {d : Type*} [Fintype d]
    (H : Matrix d d ℝ) (b : d → ℝ) (α β : ℝ) (i : d) :
    ∑ j, (ballMatrix H b α β (Sum.inl i) j) ^ 2 =
      β ^ 2 * (∑ j, (H i j) ^ 2) + (α - β * b i) ^ 2 := by
  simp only [ballMatrix, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.smul_apply, smul_eq_mul, mul_pow]
  simp [← Finset.mul_sum]

theorem ballMatrix_inr_row_sq {d : Type*} [Fintype d]
    (H : Matrix d d ℝ) (b : d → ℝ) (α β : ℝ) (i : d) :
    ∑ j, (ballMatrix H b α β (Sum.inr i) j) ^ 2 =
      β ^ 2 * (∑ j, (H i j) ^ 2) + (α + β * b i) ^ 2 := by
  simp only [ballMatrix, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, smul_eq_mul, mul_pow, neg_sq]
  simp [← Finset.mul_sum]

/-- Actual row squared-norm normalization, including the sign flip `A = -C`. -/
theorem ballMatrix_normalized {d : ℕ} (hd : 1 ≤ d)
    (H : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) {κ α β : ℝ}
    (hκ : 1 ≤ κ) (hβ : β = 1 / (4 * κ)) (hα : α = β / (8 * Real.sqrt d))
    (hH : ∀ i, ∑ j, (H i j) ^ 2 ≤ κ ^ 2)
    (hb : ∑ i, (b i) ^ 2 ≤ 1) :
    ∀ i, (∑ j, (ballMatrix H b α β i j) ^ 2 ≤ 5 / 16) ∧
      (∑ j, ((-ballMatrix H b α β) i j) ^ 2 < 1) := by
  obtain ⟨hbp, hbupper, hprod, hap, haupper⟩ := parameter_bounds hd hκ hβ hα
  have hbcoord (i : Fin d) : (b i) ^ 2 ≤ 1 := by
    apply le_trans (Finset.single_le_sum (fun j _ => sq_nonneg (b j)) (Finset.mem_univ i)) hb
  intro i
  have hrow : ∑ j, (ballMatrix H b α β i j) ^ 2 ≤ 5 / 16 := by
    cases i with
    | inl i =>
      rw [ballMatrix_inl_row_sq]
      exact (row_square_bound hbp hbupper hprod hap haupper (hH i) (hbcoord i)).1
    | inr i =>
      rw [ballMatrix_inr_row_sq]
      exact (row_square_bound hbp hbupper hprod hap haupper (hH i) (hbcoord i)).2
  refine ⟨hrow, ?_⟩
  simp only [Matrix.neg_apply, neg_sq]
  linarith

/-- Reindexing matching the sign convention of `BallReduction.rowPayoff`. -/
def signedRowIndex {d : ℕ} (j : Fin d × Bool) : Fin d ⊕ Fin d :=
  if j.2 then Sum.inr j.1 else Sum.inl j.1

/-- Pointwise bridge from the actual matrix encoding to the payoff used in
the full-gap residual-recovery theorem. -/
theorem matrix_rowPayoff {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ)
    (b z : EuclideanSpace ℝ (Fin d)) (α β s : ℝ) (j : Fin d × Bool) :
    ((-ballMatrix H (fun i => b i) α β) *ᵥ
      Sum.elim (fun i => z i) (fun _ => s)) (signedRowIndex j) =
      BallReduction.rowPayoff (Matrix.toEuclideanLin H) b α β z s j := by
  rw [Matrix.neg_mulVec, ballMatrix_mulVec]
  obtain ⟨i, sign⟩ := j
  cases sign
  · change -(α * s + β * ((H *ᵥ (fun i => z i)) i - s * b i)) =
      -α * s + β * (-1) * ((H *ᵥ (fun i => z i)) i - s * b i)
    ring
  · change -(α * s - β * ((H *ᵥ (fun i => z i)) i - s * b i)) =
      -α * s + β * 1 * ((H *ᵥ (fun i => z i)) i - s * b i)
    ring

/-- The homogeneous vector encoding preserves the Euclidean ball constraint. -/
theorem homogeneous_sq_norm {d : ℕ} (z : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    ∑ j : Fin d ⊕ Unit, (Sum.elim (fun i => z i) (fun _ => s) j) ^ 2 =
      ‖z‖ ^ 2 + s ^ 2 := by
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Finset.sum_const, Finset.card_univ, Fintype.card_unique, one_smul]
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp only [Real.norm_eq_abs, sq_abs]

theorem homogeneous_feasible_iff {d : ℕ} (z : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    (∑ j : Fin d ⊕ Unit, (Sum.elim (fun i => z i) (fun _ => s) j) ^ 2 ≤ 1) ↔
      BallReduction.Feasible z s := by
  rw [homogeneous_sq_norm]
  rfl

/-- For a square matrix, the lower singular-value inequality alone supplies
the norm-one solution hypothesis of `BallReduction.fullGap_residual`. -/
theorem source_solution_of_matrix_lower_bound {d : ℕ}
    (H : Matrix (Fin d) (Fin d) ℝ) (b : EuclideanSpace ℝ (Fin d))
    (hlower : ∀ z, ‖z‖ ≤ ‖Matrix.toEuclideanLin H z‖) (hb : ‖b‖ ≤ 1) :
    ∃ zstar, Matrix.toEuclideanLin H zstar = b ∧ ‖zstar‖ ≤ 1 := by
  have hinj : Function.Injective (Matrix.toEuclideanLin H) := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    simpa only [map_sub, hxy, sub_self, norm_zero] using hlower (x - y)
  exact BallReduction.source_solution_of_surjective_lower_bound _
    (LinearMap.surjective_of_injective hinj) hlower hb

end BallNormalization
end Matvec
