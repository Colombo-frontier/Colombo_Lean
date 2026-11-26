import MinimaxAudit.Model

/-!
Actual primal/dual paired frame in the Euclidean L2 product, with the saddle
signature acting by pair exchange. This is the signed-reversal mechanism in
manuscript equations(rorder) and(signature-reversal); dual reverse ordering is
an index permutation of this explicit sum-index representation.
-/
open scoped RealInnerProductSpace
namespace MinimaxAudit

section Paired
variable {n dx dy : ℕ}

/-- Direct Euclidean product has the sum inner product. -/
theorem paired_inner_join (x x' : Primal dx) (y y' : Dual dy) :
    inner ℝ (joinBlocks x y) (joinBlocks x' y') = inner ℝ x x' + inner ℝ y y' := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, joinBlocks, Fintype.sum_sum_type]

noncomputable def pairedPlus (U : Fin n → Primal dx) (V : Fin n → Dual dy)
    (i : Fin n) : SaddleSpace dx dy :=
  (Real.sqrt 2)⁻¹ • joinBlocks (U i) (V i)

noncomputable def pairedMinus (U : Fin n → Primal dx) (V : Fin n → Dual dy)
    (i : Fin n) : SaddleSpace dx dy :=
  (Real.sqrt 2)⁻¹ • joinBlocks (U i) (-V i)

noncomputable def pairedFrame (U : Fin n → Primal dx) (V : Fin n → Dual dy) :
    Fin n ⊕ Fin n → SaddleSpace dx dy := Sum.elim (pairedPlus U V) (pairedMinus U V)

theorem sqrt_two_inv_sq : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = 1 / 2 := by
  rw [inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem paired_frame_orthonormal {U : Fin n → Primal dx} {V : Fin n → Dual dy}
    (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V) : Orthonormal ℝ (pairedFrame U V) := by
  rw [orthonormal_iff_ite]
  intro i j
  have hUi := orthonormal_iff_ite.mp hU
  have hVi := orthonormal_iff_ite.mp hV
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp only [pairedFrame, Sum.elim_inl, pairedPlus, real_inner_smul_left,
        real_inner_smul_right, paired_inner_join, hUi, hVi, Sum.inl.injEq]
      split_ifs <;> nlinarith [sqrt_two_inv_sq]
    | inr j =>
      simp only [pairedFrame, Sum.elim_inl, Sum.elim_inr, pairedPlus, pairedMinus,
        real_inner_smul_left, real_inner_smul_right, paired_inner_join, inner_neg_right,
        hUi, hVi, reduceCtorEq, if_false]
      ring
  | inr i =>
    cases j with
    | inl j =>
      simp only [pairedFrame, Sum.elim_inl, Sum.elim_inr, pairedPlus, pairedMinus,
        real_inner_smul_left, real_inner_smul_right, paired_inner_join, inner_neg_left,
        hUi, hVi, reduceCtorEq, if_false]
      ring
    | inr j =>
      simp only [pairedFrame, Sum.elim_inr, pairedMinus, real_inner_smul_left,
        real_inner_smul_right, paired_inner_join, inner_neg_left, inner_neg_right,
        neg_neg, hUi, hVi, Sum.inr.injEq]
      split_ifs <;> nlinarith [sqrt_two_inv_sq]

theorem saddle_sign_paired_plus (U : Fin n → Primal dx) (V : Fin n → Dual dy) (i : Fin n) :
    euclideanSaddleSign dx dy (pairedPlus U V i) = pairedMinus U V i := by
  ext j
  cases j <;> simp [euclideanSaddleSign, pairedPlus, pairedMinus, joinBlocks]

theorem saddle_sign_paired_minus (U : Fin n → Primal dx) (V : Fin n → Dual dy) (i : Fin n) :
    euclideanSaddleSign dx dy (pairedMinus U V i) = pairedPlus U V i := by
  ext j
  cases j <;> simp [euclideanSaddleSign, pairedPlus, pairedMinus, joinBlocks]

/-- The saddle signature exchanges paired frame vectors exactly. -/
theorem saddle_sign_paired_frame (U : Fin n → Primal dx) (V : Fin n → Dual dy)
    (i : Fin n ⊕ Fin n) :
    euclideanSaddleSign dx dy (pairedFrame U V i) = pairedFrame U V i.swap := by
  cases i with
  | inl i => exact saddle_sign_paired_plus U V i
  | inr i => exact saddle_sign_paired_minus U V i

/-- Matrix coefficient version of W^T S W, with the paired sum index. -/
theorem paired_signed_metric {U : Fin n → Primal dx} {V : Fin n → Dual dy}
    (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V) (i j : Fin n ⊕ Fin n) :
    inner ℝ (pairedFrame U V i) (euclideanSaddleSign dx dy (pairedFrame U V j)) =
      if i = j.swap then 1 else 0 := by
  rw [saddle_sign_paired_frame]
  exact orthonormal_iff_ite.mp (paired_frame_orthonormal hU hV) i j.swap

/-- The a_i coordinate of the paper. -/
theorem paired_plus_coordinate (U : Fin n → Primal dx) (V : Fin n → Dual dy)
    (i : Fin n) (x : Primal dx) (y : Dual dy) :
    inner ℝ (pairedPlus U V i) (joinBlocks x y) =
      (inner ℝ (U i) x + inner ℝ (V i) y) / Real.sqrt 2 := by
  rw [pairedPlus, real_inner_smul_left, paired_inner_join]
  ring

/-- The b_i coordinate of the paper. -/
theorem paired_minus_coordinate (U : Fin n → Primal dx) (V : Fin n → Dual dy)
    (i : Fin n) (x : Primal dx) (y : Dual dy) :
    inner ℝ (pairedMinus U V i) (joinBlocks x y) =
      (inner ℝ (U i) x - inner ℝ (V i) y) / Real.sqrt 2 := by
  rw [pairedMinus, real_inner_smul_left, paired_inner_join, inner_neg_left]
  ring

end Paired
end MinimaxAudit
