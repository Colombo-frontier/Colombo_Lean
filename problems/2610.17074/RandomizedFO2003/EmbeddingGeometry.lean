import RandomizedFO2003.ProjectedSphere

namespace RandomizedFO2003.Rotations

variable {S T E : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def embeddingComplement (L : S →ₗᵢ[ℝ] E) : Submodule ℝ E := (LinearMap.range L.toLinearMap)ᗮ

theorem mem_embeddingComplement (L : S →ₗᵢ[ℝ] E) (x : E) :
    x ∈ embeddingComplement L ↔ L.toContinuousLinearMap.adjoint x = 0 := by
  constructor
  · intro hx
    apply ext_inner_left ℝ
    intro y
    rw [ContinuousLinearMap.adjoint_inner_right, inner_zero_right]
    exact (Submodule.mem_orthogonal _ _).mp hx (L y) ⟨y, rfl⟩
  · intro hx
    apply (Submodule.mem_orthogonal _ _).mpr
    rintro y ⟨z, rfl⟩
    change inner (𝕜 := ℝ) (L.toContinuousLinearMap z) x = 0
    rw [← ContinuousLinearMap.adjoint_inner_right L.toContinuousLinearMap z x, hx, inner_zero_right]

theorem sub_embedding_adjoint_mem (L : S →ₗᵢ[ℝ] E) (g : E) :
    g - L (L.toContinuousLinearMap.adjoint g) ∈ embeddingComplement L := by
  rw [mem_embeddingComplement, map_sub, embedding_adjoint_self, sub_self]

/-- The embedded normalized projection lies in the old complement plus the
single ambient vector used to generate it. -/
theorem projectedDirection_mem_sup (L : S →ₗᵢ[ℝ] E) (g : E) :
    L (Spherical.projectedDirection L g) ∈ embeddingComplement L ⊔ Submodule.span ℝ {g} := by
  have hg : g ∈ embeddingComplement L ⊔ Submodule.span ℝ {g} :=
    (show Submodule.span ℝ {g} ≤ embeddingComplement L ⊔ Submodule.span ℝ {g} from le_sup_right)
      (Submodule.mem_span_singleton_self g)
  have hc : g - L (L.toContinuousLinearMap.adjoint g) ∈ embeddingComplement L ⊔ Submodule.span ℝ {g} :=
    (show embeddingComplement L ≤ embeddingComplement L ⊔ Submodule.span ℝ {g} from le_sup_left)
      (sub_embedding_adjoint_mem L g)
  have hp : L (L.toContinuousLinearMap.adjoint g) ∈ embeddingComplement L ⊔ Submodule.span ℝ {g} := by
    simpa only [sub_sub_cancel] using (embeddingComplement L ⊔ Submodule.span ℝ {g}).sub_mem hg hc
  change L (‖L.toContinuousLinearMap.adjoint g‖⁻¹ • L.toContinuousLinearMap.adjoint g) ∈ _
  rw [map_smul]
  exact Submodule.smul_mem _ _ hp

theorem embeddingComplement_le_comp (L : S →ₗᵢ[ℝ] E) (J : T →ₗᵢ[ℝ] S) :
    embeddingComplement L ≤ embeddingComplement (L.comp J) := by
  intro x hx
  rw [mem_embeddingComplement] at hx ⊢
  change (L.toContinuousLinearMap.comp J.toContinuousLinearMap).adjoint x = 0
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply, hx, map_zero]

/-- Exposing one coordinate adds exactly one embedded direction to the known
complement, even if the original embedding is not onto the ambient space. -/
theorem embeddingComplement_refine (L : S →ₗᵢ[ℝ] E) (e : S) (B : Rotation S) :
    embeddingComplement (L.comp (complementEmbedding e B)) =
      embeddingComplement L ⊔ Submodule.span ℝ {L (isometry S B e)} := by
  apply le_antisymm
  · intro x hx
    have hx' := (mem_embeddingComplement _ _).mp hx
    change (L.toContinuousLinearMap.comp (complementEmbedding e B).toContinuousLinearMap).adjoint x = 0 at hx'
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply,
      complementEmbedding_adjoint, ContinuousLinearMap.comp_apply] at hx'
    let z := (isometry S B).symm (L.toContinuousLinearMap.adjoint x)
    have hz : z ∈ Submodule.span ℝ {e} := by
      have hp : (Submodule.span ℝ {e})ᗮ.orthogonalProjection z = 0 := hx'
      simpa only [Submodule.orthogonal_orthogonal] using
        (Submodule.orthogonalProjection_eq_zero_iff.mp hp)
    rcases Submodule.mem_span_singleton.mp hz with ⟨c, hc⟩
    have hv : L (L.toContinuousLinearMap.adjoint x) = c • L (isometry S B e) := by
      have hrecover : isometry S B z = L.toContinuousLinearMap.adjoint x :=
        (isometry S B).apply_symm_apply _
      rw [← hrecover, ← hc, map_smul, map_smul]
    have hmem : L (L.toContinuousLinearMap.adjoint x) ∈ Submodule.span ℝ {L (isometry S B e)} := by
      rw [hv]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    have hsum := (embeddingComplement L ⊔ Submodule.span ℝ {L (isometry S B e)}).add_mem
      ((show embeddingComplement L ≤ embeddingComplement L ⊔ Submodule.span ℝ {L (isometry S B e)}
        from le_sup_left) (sub_embedding_adjoint_mem L x))
      ((show Submodule.span ℝ {L (isometry S B e)} ≤ embeddingComplement L ⊔ Submodule.span ℝ {L (isometry S B e)}
        from le_sup_right) hmem)
    simpa only [sub_add_cancel] using hsum
  · apply sup_le (embeddingComplement_le_comp L _)
    apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    change L (isometry S B e) ∈ embeddingComplement (L.comp (complementEmbedding e B))
    rw [mem_embeddingComplement]
    change (L.toContinuousLinearMap.comp (complementEmbedding e B).toContinuousLinearMap).adjoint
      (L (isometry S B e)) = 0
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply,
      embedding_adjoint_self, complementEmbedding_adjoint, ContinuousLinearMap.comp_apply]
    change (Submodule.span ℝ {e})ᗮ.orthogonalProjection ((isometry S B).symm (isometry S B e)) = 0
    rw [LinearIsometryEquiv.symm_apply_apply]
    exact Submodule.orthogonalProjection_eq_zero_iff.mpr
      ((Submodule.span ℝ {e}).le_orthogonal_orthogonal (Submodule.mem_span_singleton_self e))

theorem embeddingComplement_reindex (L : S →ₗᵢ[ℝ] E) (V : T ≃ₗᵢ[ℝ] S) :
    embeddingComplement (L.comp V.toLinearIsometry) = embeddingComplement L := by
  apply le_antisymm
  · intro x hx
    rw [mem_embeddingComplement] at hx ⊢
    change (L.toContinuousLinearMap.comp (V : T →L[ℝ] S)).adjoint x = 0 at hx
    rw [ContinuousLinearMap.adjoint_comp, V.adjoint_eq_symm, ContinuousLinearMap.comp_apply] at hx
    exact V.symm.injective (by simpa using hx)
  · exact embeddingComplement_le_comp L _

end RandomizedFO2003.Rotations
