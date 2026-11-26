import MatchingBounds1005.GaussianBlockRows

/-! Spans of genuine rows supported in one of two coordinate blocks. -/
set_option autoImplicit false
noncomputable section

namespace MatchingBounds1005.GaussianPureRows
open GaussianVector GaussianBlockProjection

variable {a b : ℕ} {ι : Type*}

def Pure (z : Vec (a + b)) : Prop :=
  (splitLinearEquiv a b z).1 = 0 ∨ (splitLinearEquiv a b z).2 = 0

theorem pure_zero : Pure (0 : Vec (a + b)) := Or.inl (by rw [map_zero]; rfl)

theorem pure_smul (c : ℝ) (z : Vec (a + b)) (hz : Pure z) : Pure (c • z) := by
  rcases hz with h | h
  · left
    rw [map_smul]
    change c • (splitLinearEquiv a b z).1 = 0
    rw [h, smul_zero]
  · right
    rw [map_smul]
    change c • (splitLinearEquiv a b z).2 = 0
    rw [h, smul_zero]

/-- Accumulated pure-channel rows have exactly the product of their two
coordinate row spans; no cross-channel constraint is introduced. -/
theorem span_pure_rows (rows : ι → Vec (a + b)) (hp : ∀ i, Pure (rows i)) :
    Submodule.span ℝ (Set.range rows) =
      blockSpace
        (Submodule.span ℝ (Set.range (fun i => (splitLinearEquiv a b (rows i)).1)))
        (Submodule.span ℝ (Set.range (fun i => (splitLinearEquiv a b (rows i)).2))) := by
  let K := Submodule.span ℝ (Set.range rows)
  let eL : Vec a →ₗ[ℝ] Vec (a + b) :=
    (splitLinearEquiv a b).symm.toLinearMap.comp (LinearMap.inl ℝ (Vec a) (Vec b))
  let eR : Vec b →ₗ[ℝ] Vec (a + b) :=
    (splitLinearEquiv a b).symm.toLinearMap.comp (LinearMap.inr ℝ (Vec a) (Vec b))
  have hLi (i : ι) : eL (splitLinearEquiv a b (rows i)).1 ∈ K := by
    rcases hp i with h | h
    · rw [h, map_zero]
      exact Submodule.zero_mem _
    · have he : eL (splitLinearEquiv a b (rows i)).1 = rows i := by
        change (splitLinearEquiv a b).symm ((splitLinearEquiv a b (rows i)).1, 0) = rows i
        rw [← h]
        exact (splitLinearEquiv a b).symm_apply_apply (rows i)
      rw [he]
      exact Submodule.subset_span ⟨i, rfl⟩
  have hRi (i : ι) : eR (splitLinearEquiv a b (rows i)).2 ∈ K := by
    rcases hp i with h | h
    · have he : eR (splitLinearEquiv a b (rows i)).2 = rows i := by
        change (splitLinearEquiv a b).symm (0, (splitLinearEquiv a b (rows i)).2) = rows i
        rw [← h]
        exact (splitLinearEquiv a b).symm_apply_apply (rows i)
      rw [he]
      exact Submodule.subset_span ⟨i, rfl⟩
    · rw [h, map_zero]
      exact Submodule.zero_mem _
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨Submodule.subset_span ⟨i, rfl⟩, Submodule.subset_span ⟨i, rfl⟩⟩
  · have hL : Submodule.span ℝ (Set.range (fun i => (splitLinearEquiv a b (rows i)).1)) ≤ K.comap eL := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hLi i
    have hR : Submodule.span ℝ (Set.range (fun i => (splitLinearEquiv a b (rows i)).2)) ≤ K.comap eR := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hRi i
    intro z hz
    obtain ⟨hzL, hzR⟩ := (mem_blockSpace _ _ z).mp hz
    have hm := K.add_mem (hL hzL) (hR hzR)
    have he : eL (splitLinearEquiv a b z).1 + eR (splitLinearEquiv a b z).2 = z := by
      change (splitLinearEquiv a b).symm ((splitLinearEquiv a b z).1, 0) +
        (splitLinearEquiv a b).symm (0, (splitLinearEquiv a b z).2) = z
      rw [← map_add]
      simpa using (splitLinearEquiv a b).symm_apply_apply z
    rw [he] at hm
    exact hm

end MatchingBounds1005.GaussianPureRows
