import NCBall.ProjectionUpdate

/-! # The amount of hidden-vector information in one noisy innovation -/

noncomputable section
open scoped InnerProductSpace
namespace NCBall

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem residualProjection_norm_le {Q : E →L[ℝ] E} (hQ : IsResidualProjection Q) (x : E) :
    ‖Q x‖ ≤ ‖x‖ := by
  have he := hQ.2 (Q x) x
  rw [hQ.1, real_inner_self_eq_norm_sq] at he
  have hc := real_inner_le_norm (Q x) x
  nlinarith [norm_nonneg (Q x), norm_nonneg x]

theorem residualUpdate_fixed_iff {Q : E →L[ℝ] E} (hQ : IsResidualProjection Q) (a x : E) :
    residualUpdate Q a x = x ↔ Q x = x ∧ ⟪a, x⟫_ℝ = 0 := by
  constructor
  · intro hx
    have hc : Q (residualUpdate Q a x) = residualUpdate Q a x := by
      simp only [residualUpdate, ContinuousLinearMap.sub_apply, map_sub, hQ.1,
        (projection_update_commutes hQ a x).1]
    refine ⟨?_, ?_⟩
    · rwa [hx] at hc
    · have hi := residualUpdate_query_zero hQ a x
      rwa [hx] at hi
  · rintro ⟨hx, hi⟩
    have hb : ⟪Q a, x⟫_ℝ = 0 := by rw [hQ.2, hx, hi]
    simp [residualUpdate, ContinuousLinearMap.sub_apply, rankProjection_apply, hb, hx]

def normalizedInnovation (Q : E →L[ℝ] E) (a : E) : E := ‖Q a‖⁻¹ • Q a

theorem normalizedInnovation_eq_of_rescale (Q : E →L[ℝ] E) (a b : E)
    {c : ℝ} (hc : 0 < c) (he : Q a = c • Q b) :
    normalizedInnovation Q a = normalizedInnovation Q b := by
  simp only [normalizedInnovation, he, norm_smul, Real.norm_eq_abs,
    abs_of_pos hc, mul_inv_rev, smul_smul]
  rw [mul_assoc, inv_mul_cancel₀ hc.ne', mul_one]

/-- A fresh unit noise direction is unobserved and has no hidden-vector
component. Its independent contribution forces the normalized innovation
to reveal at most 1/σ² units of hidden projection energy. -/
theorem noisy_innovation_energy_bound (T : E →L[ℝ] F)
    (hT : ∀ x, ‖T x‖ ≤ ‖x‖) {Q : E →L[ℝ] E} (hQ : IsResidualProjection Q)
    (u z : E) (hu : ‖u‖ ≤ 1) (hz : ‖z‖ = 1) (huz : ⟪u, z⟫_ℝ = 0)
    (hQz : Q z = z) (hTz : T z = 0) {σ : ℝ} (hσ : 0 < σ) :
    ‖T (normalizedInnovation Q (u + σ • z))‖ ^ 2 ≤ 1 / σ ^ 2 := by
  have hb : Q (u + σ • z) = Q u + σ • z := by simp [map_add, map_smul, hQz]
  have horth : ⟪Q u, σ • z⟫_ℝ = 0 := by rw [inner_smul_right, hQ.2, hQz, huz, mul_zero]
  have hn : ‖Q (u + σ • z)‖ ^ 2 = ‖Q u‖ ^ 2 + σ ^ 2 := by
    have hadd := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hσ, hz, mul_one] at hadd
    rw [hb]
    nlinarith
  have hbn : σ ≤ ‖Q (u + σ • z)‖ := by nlinarith [sq_nonneg ‖Q u‖, norm_nonneg (Q (u + σ • z))]
  have hbp : 0 < ‖Q (u + σ • z)‖ := hσ.trans_le hbn
  have hTb : ‖T (Q (u + σ • z))‖ ≤ 1 := by
    rw [hb, map_add, map_smul, hTz, smul_zero, add_zero]
    exact (hT (Q u)).trans ((residualProjection_norm_le hQ u).trans hu)
  have hnorm : ‖T (normalizedInnovation Q (u + σ • z))‖ ≤ 1 / σ := by
    rw [normalizedInnovation, map_smul, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hbp)]
    calc
      _ ≤ ‖Q (u + σ • z)‖⁻¹ * 1 := mul_le_mul_of_nonneg_left hTb (by positivity)
      _ ≤ 1 / σ := by simpa only [mul_one, one_div] using one_div_le_one_div_of_le hσ hbn
  have hsq := mul_self_le_mul_self (norm_nonneg _) hnorm
  simpa only [← sq, div_pow, one_pow] using hsq

end NCBall
