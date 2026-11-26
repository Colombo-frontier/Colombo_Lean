import RandomizedFO2003.EmbeddingGeometry
import RandomizedFO2003.StandardExposure

namespace RandomizedFO2003.Rotations

variable {E S T : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]

/-- The known operator and its adjoint take values in the exposed physical and
latent subspaces. This invariant links frame updates to information spaces. -/
structure ExposureFrame.KnownSupport (F : ExposureFrame S E) : Prop where
  physical : ∀ x, F.known x ∈ embeddingComplement F.physical
  latent : ∀ x, F.known.adjoint x ∈ embeddingComplement F.latent

theorem ExposureFrame.initial_knownSupport :
    (ExposureFrame.initial : ExposureFrame E E).KnownSupport := by
  constructor <;> intro x <;> simp [ExposureFrame.initial, map_zero, Submodule.zero_mem]

theorem ExposureFrame.KnownSupport.refine {F : ExposureFrame S E} (hF : F.KnownSupport)
    (e : S) (A B : Rotation S) : (F.refine e A B).KnownSupport := by
  constructor
  · intro x
    change F.known x + rankOne (F.physical (isometry S A e)) (F.latent (isometry S B e)) x ∈
      embeddingComplement (F.physical.comp (complementEmbedding e A))
    rw [embeddingComplement_refine, rankOne_apply]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hF.physical x))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
  · intro x
    change (F.known + rankOne (F.physical (isometry S A e)) (F.latent (isometry S B e))).adjoint x ∈
      embeddingComplement (F.latent.comp (complementEmbedding e B))
    rw [map_add, ContinuousLinearMap.add_apply, rankOne_adjoint, rankOne_apply, embeddingComplement_refine]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hF.latent x))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))

theorem ExposureFrame.KnownSupport.reindex {F : ExposureFrame S E} (hF : F.KnownSupport)
    (V : S ≃ₗᵢ[ℝ] T) : (F.reindex V).KnownSupport := by
  constructor
  · intro x
    change F.known x ∈ embeddingComplement (F.physical.comp V.symm.toLinearIsometry)
    rw [embeddingComplement_reindex]
    exact hF.physical x
  · intro x
    change F.known.adjoint x ∈ embeddingComplement (F.latent.comp V.symm.toLinearIsometry)
    rw [embeddingComplement_reindex]
    exact hF.latent x

theorem ExposureFrame.KnownSupport.standardNext {n : ℕ} {F : ExposureFrame (Coordinates (n + 1)) E}
    (hF : F.KnownSupport) (kind : ExposureKind) (x : E) (ξ : Coordinates (n + 1)) :
    (F.standardNext kind x ξ).KnownSupport := by
  cases kind with
  | query => exact (hF.refine _ _ _).reindex _
  | response => exact (hF.refine _ _ _).reindex _

theorem ExposureFrame.afterQuery_latentComplement (F : ExposureFrame S E)
    (e : S) (he : ‖e‖ = 1) (x : E) (ξ : S) (hξ : ‖ξ‖ = 1) :
    embeddingComplement (F.afterQuery e x ξ).latent =
      embeddingComplement F.latent ⊔ Submodule.span ℝ {F.latent ξ} := by
  change embeddingComplement (F.latent.comp (complementEmbedding e (householder (e - ξ)))) = _
  rw [embeddingComplement_refine, householder_sends e ξ (he.trans hξ.symm)]

theorem ExposureFrame.afterResponse_latentComplement (F : ExposureFrame S E)
    (e : S) (he : ‖e‖ = 1) (y : E) (ξ : S) :
    embeddingComplement (F.afterResponse e y ξ).latent =
      embeddingComplement F.latent ⊔ Submodule.span ℝ {F.latent (F.responseDirection e y)} := by
  change embeddingComplement (F.latent.comp
    (complementEmbedding e (householder (e - F.responseDirection e y)))) = _
  rw [embeddingComplement_refine, householder_sends e (F.responseDirection e y)
    (he.trans (unitQueryDirection_norm e he _).symm)]

theorem ExposureFrame.afterQuery_ambient_span (F : ExposureFrame S E)
    (e : S) (he : ‖e‖ = 1) (x g : E) (hg : F.latent.toContinuousLinearMap.adjoint g ≠ 0) :
    embeddingComplement (F.afterQuery e x (Spherical.projectedDirection F.latent g)).latent ≤
      embeddingComplement F.latent ⊔ Submodule.span ℝ {g} := by
  rw [F.afterQuery_latentComplement e he x (Spherical.projectedDirection F.latent g)
    (Spherical.radial_norm S hg)]
  apply sup_le le_sup_left
  apply Submodule.span_le.mpr
  intro v hv
  rcases Set.mem_singleton_iff.mp hv with rfl
  exact projectedDirection_mem_sup F.latent g

theorem ExposureFrame.afterResponse_span (F : ExposureFrame S E)
    (e : S) (he : ‖e‖ = 1) (y : E) (ξ : S) (hy : F.latent.toContinuousLinearMap.adjoint y ≠ 0) :
    embeddingComplement (F.afterResponse e y ξ).latent ≤
      embeddingComplement F.latent ⊔ Submodule.span ℝ {y} := by
  rw [F.afterResponse_latentComplement e he]
  apply sup_le le_sup_left
  apply Submodule.span_le.mpr
  intro v hv
  rcases Set.mem_singleton_iff.mp hv with rfl
  change F.latent (unitQueryDirection e (F.latent.toContinuousLinearMap.adjoint y)) ∈ _
  rw [unitQueryDirection, if_neg hy]
  exact projectedDirection_mem_sup F.latent y

/-- The returned latent query is contained in the newly exposed latent space,
not merely in the sum of abstract coordinate spaces. -/
theorem ExposureFrame.KnownSupport.queryValue_mem {F : ExposureFrame S E} (hF : F.KnownSupport)
    (e : S) (he : ‖e‖ = 1) (x : E) (ξ : S) (hξ : ‖ξ‖ = 1) :
    F.known.adjoint x + ‖F.physical.toContinuousLinearMap.adjoint x‖ • F.latent ξ ∈
      embeddingComplement (F.afterQuery e x ξ).latent := by
  rw [F.afterQuery_latentComplement e he x ξ hξ]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (hF.latent x))
    (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))

/-- A requested latent vector becomes exposed after a forward response, even
when its previously unexposed component was zero. -/
theorem ExposureFrame.afterResponse_request_mem (F : ExposureFrame S E)
    (e : S) (he : ‖e‖ = 1) (y : E) (ξ : S) :
    y ∈ embeddingComplement (F.afterResponse e y ξ).latent := by
  rw [F.afterResponse_latentComplement e he]
  have hc : y - F.latent (F.latent.toContinuousLinearMap.adjoint y) ∈
      embeddingComplement F.latent ⊔ Submodule.span ℝ {F.latent (F.responseDirection e y)} :=
    Submodule.mem_sup_left (sub_embedding_adjoint_mem F.latent y)
  have hv : F.latent (F.latent.toContinuousLinearMap.adjoint y) =
      ‖F.latent.toContinuousLinearMap.adjoint y‖ • F.latent (F.responseDirection e y) := by
    rw [← map_smul]
    exact congrArg F.latent (norm_smul_unitQueryDirection e _).symm
  have hm : F.latent (F.latent.toContinuousLinearMap.adjoint y) ∈
      embeddingComplement F.latent ⊔ Submodule.span ℝ {F.latent (F.responseDirection e y)} := by
    rw [hv]
    exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  simpa only [sub_add_cancel] using Submodule.add_mem _ hc hm

end RandomizedFO2003.Rotations
