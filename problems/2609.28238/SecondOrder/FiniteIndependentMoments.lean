import SecondOrder.FiniteProductEntropy

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {ι α : Type*} [Fintype ι] [Fintype α]

theorem finitePiPMF_product_mean (p : ι → PMF α) (X : ι → α → ℝ) :
    pmfMean (finitePiPMF p) (fun w => ∏ i, X i (w i)) = ∏ i, pmfMean (p i) (X i) := by
  simp only [pmfMean, smul_eq_mul, finitePiPMF_toReal, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => (p i a).toReal*X i a)).symm

theorem finitePiPMF_two_coordinate_mean (p : ι → PMF α) (i j : ι) (hij : i ≠ j)
    (X Y : α → ℝ) :
    pmfMean (finitePiPMF p) (fun w => X (w i)*Y (w j)) = pmfMean (p i) X*pmfMean (p j) Y := by
  let Z : ι → α → ℝ := fun k a => (if k=i then X a else 1)*(if k=j then Y a else 1)
  have he (w : ι → α) : (∏ k, Z k (w k)) = X (w i)*Y (w j) := by
    dsimp only [Z]
    rw [Finset.prod_mul_distrib]
    simp
  have hm (k : ι) : pmfMean (p k) (Z k) =
      (if k=i then pmfMean (p i) X else 1)*(if k=j then pmfMean (p j) Y else 1) := by
    by_cases hi : k=i
    · subst k
      simp [Z, hij]
    · by_cases hj : k=j
      · subst k
        simp [Z, hi]
      · simp [Z, hi, hj]
  calc
    _ = pmfMean (finitePiPMF p) (fun w => ∏ k, Z k (w k)) := pmfMean_congr _ (fun w => (he w).symm)
    _ = ∏ k, pmfMean (p k) (Z k) := finitePiPMF_product_mean p Z
    _ = _ := by
      simp only [hm]
      rw [Finset.prod_mul_distrib]
      simp

/-- Variance adds for the actual independent finite product law. -/
theorem finitePiPMF_centered_square_sum (p : ι → PMF α) (X : ι → α → ℝ)
    (hX : ∀ i, pmfMean (p i) (X i) = 0) :
    pmfMean (finitePiPMF p) (fun w => (∑ i, X i (w i))^2) =
      ∑ i, pmfMean (p i) (fun a => X i a^2) := by
  have he (i j : ι) : pmfMean (finitePiPMF p) (fun w => X i (w i)*X j (w j)) =
      if i=j then pmfMean (p i) (fun a => X i a^2) else 0 := by
    by_cases h : i=j
    · subst j
      simpa only [if_true, ← pow_two] using finitePiPMF_coordinate_mean p i (fun a => X i a^2)
    · rw [if_neg h, finitePiPMF_two_coordinate_mean p i j h, hX, zero_mul]
  simp only [pow_two, Finset.sum_mul_sum]
  rw [pmfMean_finset_sum]
  simp only [pmfMean_finset_sum, he, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [pow_two]

end
end SecondOrder
