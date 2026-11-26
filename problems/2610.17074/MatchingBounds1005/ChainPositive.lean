import MatchingBounds1005.ChainQuadratic

/-! Positivity of the full chain Hessian, used by the inactive quadratic copies. -/
noncomputable section
open scoped BigOperators InnerProductSpace

namespace MatchingBounds1005.BlockGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (G : BlockGeometry E)

theorem chainBilinear_nonneg (n : ℕ) (z : BlockSpace (E := E) n) :
    0 ≤ G.chainBilinear n z z := by
  let u : Fin (n + 1) → ℝ := Fin.cases 0 (fun i => ⟪G.a, z i.castSucc⟫_ℝ)
  have hpair : (∑ i, u i * ⟪G.e, z i⟫_ℝ) =
      ∑ i : Fin n, ⟪G.a, z i.castSucc⟫_ℝ * ⟪G.e, z i.succ⟫_ℝ := by
    rw [Fin.sum_univ_succ]
    simp [u]
  have hsquare : (∑ i, u i ^ 2) = ∑ i : Fin n, ⟪G.a, z i.castSucc⟫_ℝ ^ 2 := by
    rw [Fin.sum_univ_succ]
    simp [u]
  have heq : (1 / 2 : ℝ) * G.chainBilinear n z z =
      ∑ i, G.quadraticBlock (u i) (z i) := by
    simp only [G.chainBilinear_apply, quadraticBlock, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, mul_assoc G.lam, ← Finset.mul_sum, ← pow_two]
    rw [hpair]
    ring
  have hsum : (∑ i, G.kappa / 2 * (⟪G.a, z i⟫_ℝ ^ 2 - u i ^ 2)) ≤
      ∑ i, G.quadraticBlock (u i) (z i) := by
    apply Finset.sum_le_sum
    intro i _
    exact G.quadraticBlock_lower _ _
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, hsquare,
    Fin.sum_univ_castSucc (fun i => ⟪G.a, z i⟫_ℝ ^ 2), ← heq] at hsum
  have hp := mul_nonneg G.kappa_nonneg (sq_nonneg ⟪G.a, z (Fin.last n)⟫_ℝ)
  nlinarith only [hsum, hp]

end MatchingBounds1005.BlockGeometry
