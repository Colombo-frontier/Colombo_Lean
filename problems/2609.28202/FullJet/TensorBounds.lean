import FullJet.RadialDerivatives

open scoped BigOperators ContDiff

namespace FullJet

section Normed
variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Unit-direction bounds imply operator-norm bounds, with zero directions
handled explicitly rather than assumed away. -/
theorem multilinear_norm_le_of_unit (f : ContinuousMultilinearMap ℝ E F)
    (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ h, (∀ i, ‖h i‖ ≤ 1) → ‖f h‖ ≤ C) : ‖f‖ ≤ C := by
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro h
  let u : ∀ i, E i := fun i => ‖h i‖⁻¹ • h i
  have hu (i : ι) : ‖u i‖ ≤ 1 := by
    by_cases hi : h i = 0
    · simp [u, hi]
    · simp [u, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hi)]
  have heq : h = fun i => ‖h i‖ • u i := by
    funext i
    by_cases hi : h i = 0
    · simp [hi, u]
    · simp [u, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hi)]
  have hnorm : ‖f h‖ = (∏ i, ‖h i‖) * ‖f u‖ := by
    calc
      _ = ‖f (fun i => ‖h i‖ • u i)‖ := congrArg (fun v => ‖f v‖) heq
      _ = _ := by
        rw [f.map_smul_univ, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (Finset.prod_nonneg (fun i hi => norm_nonneg _))]
  rw [hnorm]
  exact (mul_le_mul_of_nonneg_left (hf u hu)
    (Finset.prod_nonneg (fun i hi => norm_nonneg _))).trans_eq (mul_comm _ _)

end Normed

section Linear
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem iteratedFDeriv_linear_eq_zero (L : E →L[ℝ] F) (x : E) (k : ℕ) (hk : 2 ≤ k) :
    iteratedFDeriv ℝ k L x = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  apply norm_eq_zero.mp
  rw [show j + 2 = (j + 1) + 1 by omega, ← norm_iteratedFDeriv_fderiv]
  have hfd : fderiv ℝ L = fun _ => L := funext (fun y => L.fderiv)
  rw [hfd, iteratedFDeriv_succ_const]
  simp

end Linear

section Inner
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem iteratedFDeriv_norm_sq_eq_zero (k : ℕ) (hk : 3 ≤ k) (x : E) :
    iteratedFDeriv ℝ k (fun y : E => ‖y‖ ^ 2) x = 0 := by
  let L := ContinuousLinearMap.id ℝ E
  have h := (innerSL ℝ (E := E)).norm_iteratedFDeriv_le_of_bilinear_of_le_one
    (L.contDiff : ContDiff ℝ ∞ L) L.contDiff x (n := k) (by
      exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top)) (norm_innerSL_le ℝ)
  have hsum : (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i L x‖ * ‖iteratedFDeriv ℝ (k - i) L x‖) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hi2 : 2 ≤ i
    · rw [iteratedFDeriv_linear_eq_zero L x i hi2, norm_zero, mul_zero, zero_mul]
    · rw [iteratedFDeriv_linear_eq_zero L x (k - i) (by omega), norm_zero, mul_zero]
  rw [hsum] at h
  have heq : (fun y => (innerSL ℝ (L y)) (L y)) = fun y : E => ‖y‖ ^ 2 := by
    funext y
    exact real_inner_self_eq_norm_sq y
  rw [heq] at h
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

theorem iteratedFDeriv_quadratic_regularizer_eq_zero (lam : ℝ) (k : ℕ) (hk : 3 ≤ k) (x : E) :
    iteratedFDeriv ℝ k (fun y : E => lam / 2 * ‖y‖ ^ 2) x = 0 := by
  change iteratedFDeriv ℝ k (fun y : E => (lam / 2) • ‖y‖ ^ 2) x = 0
  rw [iteratedFDeriv_const_smul_apply' (contDiff_norm_sq ℝ).contDiffAt,
    iteratedFDeriv_norm_sq_eq_zero k hk x, smul_zero]

end Inner

end FullJet
