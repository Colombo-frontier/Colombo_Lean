import SecondOrder.Model

open scoped InnerProductSpace

namespace SecondOrder
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem normalized_inner_sq {u : E} (hu : u ≠ 0) :
    ⟪u,‖u‖⁻¹ • u⟫_ℝ^2 = ‖u‖^2 := by
  rw [inner_smul_right, real_inner_self_eq_norm_sq]
  have hn := norm_ne_zero_iff.mpr hu
  field_simp
  <;> ring

/-- An elementary replacement for the rank-two trace/eigenvalue argument. -/
theorem two_vector_large_direction (a b : E) {D : ℝ} (hD : 0 < D)
    (hab : ‖a‖^2+‖b‖^2 = D) :
    ∃ v : E, ‖v‖ = 1 ∧ D/2 ≤ ⟪a,v⟫_ℝ^2+⟪b,v⟫_ℝ^2 := by
  by_cases ha : D/2 ≤ ‖a‖^2
  · have hn : a ≠ 0 := by intro hz; simp [hz] at ha; linarith
    refine ⟨‖a‖⁻¹ • a, norm_smul_inv_norm hn, ?_⟩
    rw [normalized_inner_sq hn]
    nlinarith [sq_nonneg ⟪b,‖a‖⁻¹ • a⟫_ℝ]
  · have hb : D/2 ≤ ‖b‖^2 := by linarith
    have hn : b ≠ 0 := by intro hz; simp [hz] at hb; linarith
    refine ⟨‖b‖⁻¹ • b, norm_smul_inv_norm hn, ?_⟩
    rw [normalized_inner_sq hn]
    nlinarith [sq_nonneg ⟪a,‖b‖⁻¹ • b⟫_ℝ]

theorem two_vector_negative_direction (a b : E) (A : E →L[ℝ] E) {D : ℝ} (hD : 0 < D)
    (hab : ‖a‖^2+‖b‖^2 = D)
    (hq : ∀ v, ⟪A v,v⟫_ℝ ≤ -(D⁻¹)^2*(⟪a,v⟫_ℝ^2+⟪b,v⟫_ℝ^2)+(1/(4*D))*‖v‖^2) :
    ∃ v : E, ‖v‖ = 1 ∧ ⟪A v,v⟫_ℝ ≤ -1/(4*D) := by
  obtain ⟨v,hv,hlarge⟩ := two_vector_large_direction a b hD hab
  refine ⟨v,hv,?_⟩
  have hh := hq v
  rw [hv] at hh
  have hm := mul_le_mul_of_nonneg_left hlarge (sq_nonneg D⁻¹)
  have hid : (D⁻¹)^2*(D/2) = 1/(2*D) := by field_simp; ring
  rw [hid] at hm
  have he : 1/(2*D) = 2*(1/(4*D)) := by ring
  rw [he] at hm
  simp only [one_pow, mul_one] at hh
  rw [neg_div]
  linarith

end
end SecondOrder
