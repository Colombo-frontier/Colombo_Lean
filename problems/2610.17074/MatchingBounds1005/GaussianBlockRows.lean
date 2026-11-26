import MatchingBounds1005.GaussianBlockProjection

/-! Actual spans of simultaneous block observations. -/
set_option autoImplicit false
noncomputable section

namespace MatchingBounds1005.GaussianBlockRows
open GaussianVector GaussianBlockProjection

variable {a b : ℕ} {ι κ : Type*}

def blockRows (left : ι → Vec a) (right : κ → Vec b) : ι ⊕ κ → Vec (a + b)
  | Sum.inl i => (splitLinearEquiv a b).symm (left i, 0)
  | Sum.inr j => (splitLinearEquiv a b).symm (0, right j)

theorem span_blockRows (left : ι → Vec a) (right : κ → Vec b) :
    Submodule.span ℝ (Set.range (blockRows left right)) =
      blockSpace (Submodule.span ℝ (Set.range left)) (Submodule.span ℝ (Set.range right)) := by
  let K := Submodule.span ℝ (Set.range (blockRows left right))
  let eL : Vec a →ₗ[ℝ] Vec (a + b) :=
    (splitLinearEquiv a b).symm.toLinearMap.comp (LinearMap.inl ℝ (Vec a) (Vec b))
  let eR : Vec b →ₗ[ℝ] Vec (a + b) :=
    (splitLinearEquiv a b).symm.toLinearMap.comp (LinearMap.inr ℝ (Vec a) (Vec b))
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i | j, rfl⟩
    · change (splitLinearEquiv a b ((splitLinearEquiv a b).symm (left i, 0))).1 ∈ _ ∧
        (splitLinearEquiv a b ((splitLinearEquiv a b).symm (left i, 0))).2 ∈ _
      rw [LinearEquiv.apply_symm_apply]
      exact ⟨Submodule.subset_span ⟨i, rfl⟩, Submodule.zero_mem _⟩
    · change (splitLinearEquiv a b ((splitLinearEquiv a b).symm (0, right j))).1 ∈ _ ∧
        (splitLinearEquiv a b ((splitLinearEquiv a b).symm (0, right j))).2 ∈ _
      rw [LinearEquiv.apply_symm_apply]
      exact ⟨Submodule.zero_mem _, Submodule.subset_span ⟨j, rfl⟩⟩
  · have hL : Submodule.span ℝ (Set.range left) ≤ K.comap eL := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
    have hR : Submodule.span ℝ (Set.range right) ≤ K.comap eR := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact Submodule.subset_span ⟨Sum.inr j, rfl⟩
    intro z hz
    obtain ⟨hzL, hzR⟩ := (mem_blockSpace _ _ z).mp hz
    have hm := K.add_mem (hL hzL) (hR hzR)
    have heq : eL (splitLinearEquiv a b z).1 + eR (splitLinearEquiv a b z).2 = z := by
      change (splitLinearEquiv a b).symm ((splitLinearEquiv a b z).1, 0) +
        (splitLinearEquiv a b).symm (0, (splitLinearEquiv a b z).2) = z
      rw [← map_add]
      simpa using (splitLinearEquiv a b).symm_apply_apply z
    rw [heq] at hm
    exact hm

theorem span_scaled_rows (rows : ι → Vec a) (σ : ℝ) (hσ : σ ≠ 0) :
    Submodule.span ℝ (Set.range (fun i => σ • rows i)) = Submodule.span ℝ (Set.range rows) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.smul_mem _ σ (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hm := (Submodule.span ℝ (Set.range (fun i => σ • rows i))).smul_mem σ⁻¹
      (Submodule.subset_span ⟨i, rfl⟩)
    simpa only [smul_smul, inv_mul_cancel₀ hσ, one_smul] using hm

end MatchingBounds1005.GaussianBlockRows
