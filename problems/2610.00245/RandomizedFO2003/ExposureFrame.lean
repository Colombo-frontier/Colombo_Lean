import RandomizedFO2003.AdaptiveExposure
import Mathlib.MeasureTheory.Measure.Haar.Disintegration

namespace RandomizedFO2003.Rotations

variable {E S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]

/-- The exposed rank-one map, with physical vector first and latent vector second. -/
noncomputable def rankOne (a b : E) : E →L[ℝ] E := (innerSL ℝ b).smulRight a

omit [FiniteDimensional ℝ E] in
@[simp] theorem rankOne_apply (a b x : E) : rankOne a b x = inner (𝕜 := ℝ) b x • a := rfl

theorem rankOne_adjoint (a b : E) : (rankOne a b).adjoint = rankOne b a := by
  ext x
  apply ext_inner_right ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left, rankOne_apply, rankOne_apply,
    real_inner_smul_left, real_inner_smul_right, real_inner_comm x a]
  ring

/-- A fixed coordinate space for the still-unrevealed part, embedded separately
in physical and latent coordinates. The known map records all exposed actions. -/
structure ExposureFrame (S E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup S] [InnerProductSpace ℝ S] where
  physical : S →ₗᵢ[ℝ] E
  latent : S →ₗᵢ[ℝ] E
  known : E →L[ℝ] E

noncomputable def ExposureFrame.operator (F : ExposureFrame S E) (R : Rotation S) : E →L[ℝ] E :=
  F.known + F.physical.toContinuousLinearMap.comp
    ((R : S →L[ℝ] S).comp F.latent.toContinuousLinearMap.adjoint)

noncomputable def ExposureFrame.initial : ExposureFrame E E :=
  ⟨LinearIsometry.id, LinearIsometry.id, 0⟩

@[simp] theorem ExposureFrame.initial_operator (R : Rotation E) :
    (ExposureFrame.initial : ExposureFrame E E).operator R = (R : E →L[ℝ] E) := by
  simp [ExposureFrame.operator, ExposureFrame.initial]

noncomputable def complementEmbedding (e : S) (A : Rotation S) :
    (Submodule.span ℝ {e})ᗮ →ₗᵢ[ℝ] S :=
  (isometry S A).toLinearIsometry.comp (Submodule.span ℝ {e})ᗮ.subtypeₗᵢ

theorem complementEmbedding_adjoint (e : S) (A : Rotation S) :
    (complementEmbedding e A).toContinuousLinearMap.adjoint =
      (Submodule.span ℝ {e})ᗮ.orthogonalProjection.comp (A⁻¹ : Rotation S).val := by
  change ((A : S →L[ℝ] S).comp (Submodule.span ℝ {e})ᗮ.subtypeL).adjoint = _
  rw [ContinuousLinearMap.adjoint_comp, Submodule.adjoint_subtypeL]
  rfl

omit [FiniteDimensional ℝ S] in
theorem line_projection_rankOne (e : S) (he : ‖e‖ = 1) :
    (Submodule.span ℝ {e}).subtypeL.comp (Submodule.span ℝ {e}).orthogonalProjection = rankOne e e := by
  ext x
  change ((Submodule.span ℝ {e}).orthogonalProjection x : S) = _
  rw [Submodule.orthogonalProjection_singleton]
  simp [he, rankOne]

theorem rotation_rankOne_split (e : S) (he : ‖e‖ = 1) (A B : Rotation S)
    (R : Rotation (Submodule.span ℝ {e})ᗮ) :
    ((A * extendComplement (Submodule.span ℝ {e}) R * B⁻¹ : Rotation S) : S →L[ℝ] S) =
      rankOne (isometry S A e) (isometry S B e) +
        (complementEmbedding e A).toContinuousLinearMap.comp
          ((R : (Submodule.span ℝ {e})ᗮ →L[ℝ] (Submodule.span ℝ {e})ᗮ).comp
            (complementEmbedding e B).toContinuousLinearMap.adjoint) := by
  rw [complementEmbedding_adjoint]
  ext x
  change isometry S A (isometry S (extendComplement (Submodule.span ℝ {e}) R)
      (isometry S B⁻¹ x)) = inner (𝕜 := ℝ) (isometry S B e) x • isometry S A e +
        isometry S A (isometry (Submodule.span ℝ {e})ᗮ R
          ((Submodule.span ℝ {e})ᗮ.orthogonalProjection (isometry S B⁻¹ x)))
  rw [extendComplement_apply, map_add, Submodule.orthogonalProjection_singleton]
  simp only [he, RCLike.ofReal_real_eq_id, id_eq, one_pow, div_one, map_smul]
  congr 2
  rw [isometry_inv, ← (isometry S B).inner_map_map e ((isometry S B).symm x),
    LinearIsometryEquiv.apply_symm_apply]

theorem rankOne_comp_adjoint (P L : S →L[ℝ] E) (a b : S) :
    P.comp ((rankOne a b).comp L.adjoint) = rankOne (P a) (L b) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, rankOne_apply, map_smul,
    ContinuousLinearMap.adjoint_inner_right]

noncomputable def ExposureFrame.refine (F : ExposureFrame S E) (e : S) (A B : Rotation S) :
    ExposureFrame (Submodule.span ℝ {e})ᗮ E where
  physical := F.physical.comp (complementEmbedding e A)
  latent := F.latent.comp (complementEmbedding e B)
  known := F.known + rankOne (F.physical (isometry S A e)) (F.latent (isometry S B e))

/-- Exact state refinement after exposing one new direction. This identity is
the algebraic invariant needed to iterate the Haar decomposition. -/
theorem ExposureFrame.refine_operator (F : ExposureFrame S E) (e : S) (he : ‖e‖ = 1)
    (A B : Rotation S) (R : Rotation (Submodule.span ℝ {e})ᗮ) :
    F.operator (A * extendComplement (Submodule.span ℝ {e}) R * B⁻¹) =
      (F.refine e A B).operator R := by
  unfold ExposureFrame.operator
  rw [rotation_rankOne_split e he, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
    rankOne_comp_adjoint]
  change F.known + (rankOne (F.physical (isometry S A e)) (F.latent (isometry S B e)) + _) =
    (F.known + rankOne (F.physical (isometry S A e)) (F.latent (isometry S B e))) + _
  rw [add_assoc]
  congr 2
  change _ = (F.physical.toContinuousLinearMap.comp (complementEmbedding e A).toContinuousLinearMap).comp
    ((R : (Submodule.span ℝ {e})ᗮ →L[ℝ] (Submodule.span ℝ {e})ᗮ).comp
      (F.latent.toContinuousLinearMap.comp (complementEmbedding e B).toContinuousLinearMap).adjoint)
  rw [ContinuousLinearMap.adjoint_comp]
  ext x
  rfl

end RandomizedFO2003.Rotations
