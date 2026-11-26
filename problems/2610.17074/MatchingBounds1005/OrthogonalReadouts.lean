import MatchingBounds1005.PrimitiveBounds
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Dimension-free estimates for actual orthogonal readouts. These are the
finite-sum estimates behind the block potential's derivative budgets. -/
namespace MatchingBounds1005

open scoped BigOperators InnerProductSpace ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] (b : ι → E) (hb : Orthonormal ℝ b)

include hb in
theorem orthogonal_readout_pair (x y : E) :
    ∑ s, |⟪b s, x⟫_ℝ| * |⟪b s, y⟫_ℝ| ≤ ‖x‖ * ‖y‖ := by
  have hx : ∑ s, |⟪b s, x⟫_ℝ| ^ 2 ≤ ‖x‖ ^ 2 := by
    simpa only [Real.norm_eq_abs] using hb.sum_inner_products_le (s := Finset.univ) x
  have hy : ∑ s, |⟪b s, y⟫_ℝ| ^ 2 ≤ ‖y‖ ^ 2 := by
    simpa only [Real.norm_eq_abs] using hb.sum_inner_products_le (s := Finset.univ) y
  calc
    _ ≤ Real.sqrt (∑ s, |⟪b s, x⟫_ℝ| ^ 2) *
        Real.sqrt (∑ s, |⟪b s, y⟫_ℝ| ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _
    _ ≤ Real.sqrt (‖x‖ ^ 2) * Real.sqrt (‖y‖ ^ 2) := by
      gcongr
    _ = _ := by simp

include hb in
theorem orthogonal_readout_product (n : ℕ) (v : Fin (n + 2) → E) :
    ∑ s, ∏ j, |⟪b s, v j⟫_ℝ| ≤ ∏ j, ‖v j‖ := by
  have hpoint (s : ι) (j : Fin (n + 2)) : |⟪b s, v j⟫_ℝ| ≤ ‖v j‖ := by
    simpa only [hb.norm_eq_one s, one_mul] using abs_real_inner_le_norm (b s) (v j)
  simp only [Fin.prod_univ_succ, Fin.succ_zero_eq_one]
  calc
    _ ≤ ∑ s, |⟪b s, v 0⟫_ℝ| * (|⟪b s, v 1⟫_ℝ| *
        ∏ j : Fin n, ‖v j.succ.succ‖) := by
      apply Finset.sum_le_sum
      intro s _
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply Finset.prod_le_prod
      · intro j _; exact abs_nonneg _
      · intro j _; exact hpoint s _
    _ = (∑ s, |⟪b s, v 0⟫_ℝ| * |⟪b s, v 1⟫_ℝ|) *
        ∏ j : Fin n, ‖v j.succ.succ‖ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ ≤ (‖v 0‖ * ‖v 1‖) * ∏ j : Fin n, ‖v j.succ.succ‖ :=
      mul_le_mul_of_nonneg_right (orthogonal_readout_pair b hb _ _) (by positivity)
    _ = _ := by ring

noncomputable def ridgeSum (φ : ℝ → ℝ) (A : ℝ) (x : E) : ℝ :=
  ∑ s, φ (A * ⟪b s, x⟫_ℝ)

noncomputable def scaledReadout (A : ℝ) (s : ι) : E →L[ℝ] ℝ :=
  A • innerSL ℝ (b s)

theorem ridgeSum_smooth {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (A : ℝ) :
    ContDiff ℝ ∞ (ridgeSum b φ A) := by
  apply ContDiff.sum
  intro s _
  exact hφ.comp (scaledReadout b A s).contDiff

theorem ridgeSum_derivative_apply {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (A : ℝ) (n : ℕ) (x : E) (v : Fin n → E) :
    iteratedFDeriv ℝ n (ridgeSum b φ A) x v =
      ∑ s, iteratedDeriv n φ (A * ⟪b s, x⟫_ℝ) * A ^ n *
        ∏ j, ⟪b s, v j⟫_ℝ := by
  have hlevel : (n : WithTop ℕ∞) ≤ ∞ :=
    by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top)
  have heq : ridgeSum b φ A = fun y => ∑ s, (φ ∘ scaledReadout b A s) y := by
    funext y
    simp [ridgeSum, scaledReadout]
  rw [heq, iteratedFDeriv_sum (u := Finset.univ) (fun s _ =>
    ((hφ.comp (scaledReadout b A s).contDiff).of_le hlevel))]
  simp only [Finset.sum_apply, ContinuousMultilinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro s _
  rw [(scaledReadout b A s).iteratedFDeriv_comp_right hφ x hlevel]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
  simp only [scaledReadout, ContinuousLinearMap.smul_apply, innerSL_apply,
    smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  ring

include hb in
/-- No factor depending on the number of blocks occurs in this genuine
multilinear derivative estimate. -/
theorem ridgeSum_derivative_bound {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (A : ℝ) (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ u, |iteratedDeriv (n + 2) φ u| ≤ C) (x : E) :
    ‖iteratedFDeriv ℝ (n + 2) (ridgeSum b φ A) x‖ ≤ C * |A| ^ (n + 2) := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  rw [Real.norm_eq_abs, ridgeSum_derivative_apply b hφ]
  calc
    _ ≤ ∑ s, |iteratedDeriv (n + 2) φ (A * ⟪b s, x⟫_ℝ) * A ^ (n + 2) *
        ∏ j, ⟪b s, v j⟫_ℝ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s, (C * |A| ^ (n + 2)) * ∏ j, |⟪b s, v j⟫_ℝ| := by
      apply Finset.sum_le_sum
      intro s _
      simp only [abs_mul, abs_pow, Finset.abs_prod]
      gcongr
      exact hbound _
    _ = (C * |A| ^ (n + 2)) * (∑ s, ∏ j, |⟪b s, v j⟫_ℝ|) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (orthogonal_readout_product b hb n v) (by positivity)

include hb in
theorem potential_ridge_uniform_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ A : ℝ, ∀ x : E,
      ‖iteratedFDeriv ℝ (n + 2) (ridgeSum b (Primitive.potential r) A) x‖ ≤
        (C * r ^ 3 / r ^ (n + 1)) * |A| ^ (n + 2) := by
  obtain ⟨C, hC, hbound⟩ := Primitive.potential_derivative_bound (n + 1) (by omega)
  refine ⟨C, hC, fun r hr A x => ?_⟩
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  exact ridgeSum_derivative_bound b hb (Primitive.potential_smooth r) A n
    (C * r ^ 3 / r ^ (n + 1)) (by positivity) (hbound r hr) x

include hb in
theorem scaled_potential_ridge_uniform_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ A τ : ℝ, ∀ x : E,
      ‖iteratedFDeriv ℝ (n + 2) (fun y => τ * ridgeSum b (Primitive.potential r) A y) x‖ ≤
        |τ| * (C * r ^ 3 / r ^ (n + 1)) * |A| ^ (n + 2) := by
  obtain ⟨C, hC, hbound⟩ := potential_ridge_uniform_bound b hb n
  refine ⟨C, hC, fun r hr A τ x => ?_⟩
  have hlevel : ((n + 2 : ℕ) : WithTop ℕ∞) ≤ ∞ :=
    by
      generalize n + 2 = j
      exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top)
  have hs : ContDiffAt ℝ (n + 2 : ℕ) (ridgeSum b (Primitive.potential r) A) x :=
    ((ridgeSum_smooth b (Primitive.potential_smooth r) A).of_le hlevel).contDiffAt
  change ‖iteratedFDeriv ℝ (n + 2) (τ • ridgeSum b (Primitive.potential r) A) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply hs,
    norm_smul τ (iteratedFDeriv ℝ (n + 2) (ridgeSum b (Primitive.potential r) A) x),
    Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (hbound r hr A x) (abs_nonneg τ)).trans_eq (by ring)

end MatchingBounds1005
