import MatchingBounds1005.ChainQuadratic
import MatchingBounds1005.ChainGap

/-! Source radial inequality for the actual chain, by completing squares. -/
noncomputable section
open scoped InnerProductSpace BigOperators

namespace MatchingBounds1005.BlockGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (G : BlockGeometry E)

theorem euclideanQuadratic_lower (n : ℕ) (z : BlockSpace (E := E) n) :
    -G.kappa / 2 ≤ G.euclideanQuadratic n z := by
  have h1 := G.euclideanObjective_decomposition 1 n z
  have h2 := G.objective_eq_incoming_sum 1 n (fun i => z i)
  change G.euclideanObjective 1 n z = _ at h2
  have h3 := G.actual_quadratic_sum_lower n (fun i => z i)
  linarith only [h1, h2, h3]

theorem euclideanObjective_radial_identity (r : ℝ) (n : ℕ) (z : BlockSpace (E := E) n) :
    ⟪z, gradient (G.euclideanObjective r n) z⟫_ℝ =
      G.euclideanQuadratic n ((2 : ℝ) • z) / 2 +
        G.tau * ∑ i, ⟪G.a, z i⟫_ℝ * Primitive.slope r ⟪G.a, z i⟫_ℝ := by
  have hpair : ⟪z, gradient (G.euclideanObjective r n) z⟫_ℝ =
      G.objectiveDerivative r n (fun i => z i) (fun i => z i) := by
    rw [G.euclideanObjective_gradient, real_inner_comm (G.euclideanGradient r n z) z,
      G.objectiveDerivative_apply]
    rfl
  have hq : G.euclideanQuadratic n ((2 : ℝ) • z) / 2 =
      G.chainBilinear n z z - G.lam * G.firstEntry n z := by
    simp only [euclideanQuadratic, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hpair, hq, G.chainBilinear_apply]
  simp only [objectiveDerivative, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, innerSL_apply, readoutCLM_apply, smul_eq_mul,
    localGradient, gradientBlock, zero_mul, mul_zero, zero_smul, sub_zero,
    inner_add_left, real_inner_smul_left, firstEntry, PiLp.proj_apply,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_add, add_mul, ← Finset.mul_sum]
  have hd : (∑ i, ⟪G.H (z i), z i⟫_ℝ) = ∑ i, ⟪z i, G.H (z i)⟫_ℝ := by
    apply Finset.sum_congr rfl
    intro i _
    exact real_inner_comm _ _
  rw [hd]
  simp only [mul_assoc, ← Finset.mul_sum]
  have hp : (∑ i, Primitive.slope r ⟪G.a, z i⟫_ℝ * ⟪G.a, z i⟫_ℝ) =
      ∑ i, ⟪G.a, z i⟫_ℝ * Primitive.slope r ⟪G.a, z i⟫_ℝ := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hc : (∑ i : Fin n, ⟪G.e, z i.succ⟫_ℝ * ⟪G.a, z i.castSucc⟫_ℝ) =
      ∑ i : Fin n, ⟪G.a, z i.castSucc⟫_ℝ * ⟪G.e, z i.succ⟫_ℝ := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hp, hc]
  ring

theorem euclideanObjective_radial_lower (r : ℝ) (hr : 1 ≤ r) (n : ℕ)
    (z : BlockSpace (E := E) n) :
    -(405 / 32 : ℝ) * (n + 1 : ℕ) * G.tau - G.kappa / 4 ≤
      ⟪z, gradient (G.euclideanObjective r n) z⟫_ℝ := by
  rw [G.euclideanObjective_radial_identity]
  have hq := G.euclideanQuadratic_lower n ((2 : ℝ) • z)
  have hs : ∑ i : Fin (n + 1), -(405 / 32 : ℝ) ≤
      ∑ i, ⟪G.a, z i⟫_ℝ * Primitive.slope r ⟪G.a, z i⟫_ℝ := by
    exact Finset.sum_le_sum (fun i _ => Primitive.slope_radial hr _)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hm := mul_le_mul_of_nonneg_left hs G.tau_nonneg
  nlinarith only [hq, hm]

theorem euclideanObjective_radial_gap (r : ℝ) (hr : 1 ≤ r) (n : ℕ)
    (z : BlockSpace (E := E) n) :
    -(81 / 64 : ℝ) * (10 * (n + 1 : ℕ) * G.tau + G.kappa / 2) ≤
      ⟪z, gradient (G.euclideanObjective r n) z⟫_ℝ := by
  have h := G.euclideanObjective_radial_lower r hr n z
  have hk := G.kappa_nonneg
  nlinarith only [h, hk]

end MatchingBounds1005.BlockGeometry
