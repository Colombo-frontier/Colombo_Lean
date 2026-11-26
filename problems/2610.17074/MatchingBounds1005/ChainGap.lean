import MatchingBounds1005.BlockGradientBound

/-! Gap of the actual finite objective, with the initial boundary included. -/
noncomputable section
open scoped InnerProductSpace BigOperators

namespace MatchingBounds1005.BlockGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (G : BlockGeometry E)

theorem incoming_pair_sum (n : ℕ) (z : Fin (n + 1) → E) :
    (∑ i, G.incomingReadout z i * ⟪G.e, z i⟫_ℝ) =
      ⟪G.e, z 0⟫_ℝ + ∑ i : Fin n, ⟪G.a, z i.castSucc⟫_ℝ * ⟪G.e, z i.succ⟫_ℝ := by
  rw [Fin.sum_univ_succ]
  simp only [G.incomingReadout_zero, G.incomingReadout_succ, one_mul]

theorem incoming_square_sum (n : ℕ) (z : Fin (n + 1) → E) :
    (∑ i, (G.incomingReadout z i) ^ 2) =
      1 + ∑ i : Fin n, ⟪G.a, z i.castSucc⟫_ℝ ^ 2 := by
  rw [Fin.sum_univ_succ]
  simp only [G.incomingReadout_zero, G.incomingReadout_succ, one_pow]

theorem objective_eq_incoming_sum (r : ℝ) (n : ℕ) (z : Fin (n + 1) → E) :
    G.objective r n z = (∑ i, G.quadraticBlock (G.incomingReadout z i) (z i)) +
      G.tau * ∑ i, Primitive.potential r ⟪G.a, z i⟫_ℝ := by
  simp only [objective, localEnergy, sectionEnergy, quadraticBlock, mul_zero,
    zero_mul, sub_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_assoc G.lam, ← Finset.mul_sum]
  rw [G.incoming_pair_sum]
  ring

theorem actual_quadratic_sum_lower (n : ℕ) (z : Fin (n + 1) → E) :
    -G.kappa / 2 ≤ ∑ i, G.quadraticBlock (G.incomingReadout z i) (z i) := by
  have hsum : (∑ i, G.kappa / 2 * (⟪G.a, z i⟫_ℝ ^ 2 - (G.incomingReadout z i) ^ 2)) ≤
      ∑ i, G.quadraticBlock (G.incomingReadout z i) (z i) := by
    apply Finset.sum_le_sum
    intro i _
    exact G.quadraticBlock_lower _ _
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, G.incoming_square_sum,
    Fin.sum_univ_castSucc (fun i => ⟪G.a, z i⟫_ℝ ^ 2)] at hsum
  have hp := mul_nonneg G.kappa_nonneg (sq_nonneg ⟪G.a, z (Fin.last n)⟫_ℝ)
  nlinarith only [hsum, hp]

theorem objective_lower (r : ℝ) (n : ℕ) (z : Fin (n + 1) → E) :
    -G.kappa / 2 ≤ G.objective r n z := by
  rw [G.objective_eq_incoming_sum]
  have hp : 0 ≤ G.tau * ∑ i, Primitive.potential r ⟪G.a, z i⟫_ℝ :=
    mul_nonneg G.tau_nonneg (Finset.sum_nonneg (fun i _ => Primitive.potential_nonneg r _))
  have hq := G.actual_quadratic_sum_lower n z
  linarith

theorem objective_zero (r : ℝ) (hr : 1 ≤ r) (n : ℕ) :
    G.objective r n 0 = 10 * (n + 1 : ℕ) * G.tau := by
  simp [objective, localEnergy, sectionEnergy, quadraticBlock, Primitive.potential_zero hr]
  ring

theorem euclideanObjective_gap (r : ℝ) (hr : 1 ≤ r) (n : ℕ) (z : BlockSpace (E := E) n) :
    G.euclideanObjective r n 0 - G.euclideanObjective r n z ≤
      10 * (n + 1 : ℕ) * G.tau + G.kappa / 2 := by
  change G.objective r n 0 - G.objective r n (fun i => z i) ≤ _
  rw [G.objective_zero r hr n]
  have h := G.objective_lower r n (fun i => z i)
  linarith

end MatchingBounds1005.BlockGeometry
