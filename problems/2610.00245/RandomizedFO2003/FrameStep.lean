import RandomizedFO2003.ExposureFrame

namespace RandomizedFO2003.Rotations

variable {E S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]

noncomputable def ExposureFrame.queryDirection (F : ExposureFrame S E) (e : S) (x : E) : S :=
  unitQueryDirection e (F.physical.toContinuousLinearMap.adjoint x)

noncomputable def ExposureFrame.responseDirection (F : ExposureFrame S E) (e : S) (y : E) : S :=
  unitQueryDirection e (F.latent.toContinuousLinearMap.adjoint y)

noncomputable def ExposureFrame.querySplit (F : ExposureFrame S E) (e : S) (x : E) (R : Rotation S) :
    S × Rotation (Submodule.span ℝ {e})ᗮ :=
  splitExposure e (R⁻¹ * householder (e - F.queryDirection e x))

noncomputable def ExposureFrame.responseSplit (F : ExposureFrame S E) (e : S) (y : E) (R : Rotation S) :
    S × Rotation (Submodule.span ℝ {e})ᗮ :=
  splitExposure e (R * householder (e - F.responseDirection e y))

noncomputable def ExposureFrame.afterQuery (F : ExposureFrame S E) (e : S) (x : E) (ξ : S) :
    ExposureFrame (Submodule.span ℝ {e})ᗮ E :=
  F.refine e (householder (e - F.queryDirection e x)) (householder (e - ξ))

noncomputable def ExposureFrame.afterResponse (F : ExposureFrame S E) (e : S) (y : E) (ξ : S) :
    ExposureFrame (Submodule.span ℝ {e})ᗮ E :=
  F.refine e (householder (e - ξ)) (householder (e - F.responseDirection e y))

theorem ExposureFrame.querySplit_direction (F : ExposureFrame S E) (e : S) (he : ‖e‖ = 1)
    (x : E) (R : Rotation S) :
    (F.querySplit e x R).1 = (isometry S R).symm (F.queryDirection e x) := by
  change isometry S (R⁻¹ * householder (e - F.queryDirection e x)) e = _
  rw [isometry_mul, householder_sends e (F.queryDirection e x)
    (he.trans (unitQueryDirection_norm e he _).symm), isometry_inv]

theorem ExposureFrame.responseSplit_direction (F : ExposureFrame S E) (e : S) (he : ‖e‖ = 1)
    (y : E) (R : Rotation S) :
    (F.responseSplit e y R).1 = isometry S R (F.responseDirection e y) := by
  change isometry S (R * householder (e - F.responseDirection e y)) e = _
  rw [isometry_mul, householder_sends e (F.responseDirection e y)
    (he.trans (unitQueryDirection_norm e he _).symm)]

theorem ExposureFrame.querySplit_norm (F : ExposureFrame S E) (e : S) (he : ‖e‖ = 1)
    (x : E) (R : Rotation S) : ‖(F.querySplit e x R).1‖ = 1 := by
  rw [F.querySplit_direction e he, (isometry S R).symm.norm_map]
  exact unitQueryDirection_norm e he _

theorem ExposureFrame.responseSplit_norm (F : ExposureFrame S E) (e : S) (he : ‖e‖ = 1)
    (y : E) (R : Rotation S) : ‖(F.responseSplit e y R).1‖ = 1 := by
  rw [F.responseSplit_direction e he, (isometry S R).norm_map]
  exact unitQueryDirection_norm e he _

theorem ExposureFrame.queryStep_operator (F : ExposureFrame S E) (e : S) (he : ‖e‖ = 1)
    (x : E) (R : Rotation S) :
    F.operator R = (F.afterQuery e x (F.querySplit e x R).1).operator (F.querySplit e x R).2⁻¹ := by
  have hs := exposureSample_split e (R⁻¹ * householder (e - F.queryDirection e x))
  change householder (e - (F.querySplit e x R).1) *
    extendComplement (Submodule.span ℝ {e}) (F.querySplit e x R).2 =
      R⁻¹ * householder (e - F.queryDirection e x) at hs
  have hR : R = householder (e - F.queryDirection e x) *
      extendComplement (Submodule.span ℝ {e}) (F.querySplit e x R).2⁻¹ *
        (householder (e - (F.querySplit e x R).1))⁻¹ := by
    rw [extendComplement_inv]
    have ht := congrArg (fun Z : Rotation S => householder (e - F.queryDirection e x) * Z⁻¹) hs
    simpa only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] using ht.symm
  conv_lhs => rw [hR]
  exact F.refine_operator e he _ _ _

theorem ExposureFrame.responseStep_operator (F : ExposureFrame S E) (e : S) (he : ‖e‖ = 1)
    (y : E) (R : Rotation S) :
    F.operator R = (F.afterResponse e y (F.responseSplit e y R).1).operator (F.responseSplit e y R).2 := by
  have hs := exposureSample_split e (R * householder (e - F.responseDirection e y))
  change householder (e - (F.responseSplit e y R).1) *
    extendComplement (Submodule.span ℝ {e}) (F.responseSplit e y R).2 =
      R * householder (e - F.responseDirection e y) at hs
  have hR : R = householder (e - (F.responseSplit e y R).1) *
      extendComplement (Submodule.span ℝ {e}) (F.responseSplit e y R).2 *
        (householder (e - F.responseDirection e y))⁻¹ := by rw [hs]; group
  conv_lhs => rw [hR]
  exact F.refine_operator e he _ _ _

theorem ExposureFrame.adjoint_apply (F : ExposureFrame S E) (R : Rotation S) (x : E) :
    (F.operator R).adjoint x = F.known.adjoint x +
      F.latent ((isometry S R).symm (F.physical.toContinuousLinearMap.adjoint x)) := by
  simp only [ExposureFrame.operator, map_add, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_apply]
  rfl

/-- The new latent query is an old known vector plus a multiple of the newly
exposed latent direction. This is the local span-inclusion step. -/
theorem ExposureFrame.query_vector (F : ExposureFrame S E) (e : S) (he : ‖e‖ = 1)
    (x : E) (R : Rotation S) :
    (F.operator R).adjoint x = F.known.adjoint x +
      ‖F.physical.toContinuousLinearMap.adjoint x‖ • F.latent (F.querySplit e x R).1 := by
  rw [F.adjoint_apply, F.querySplit_direction e he, ← map_smul, ← map_smul]
  congr 3
  exact (norm_smul_unitQueryDirection e _).symm

theorem ExposureFrame.response_vector (F : ExposureFrame S E) (e : S) (he : ‖e‖ = 1)
    (y : E) (R : Rotation S) :
    F.operator R y = F.known y +
      ‖F.latent.toContinuousLinearMap.adjoint y‖ • F.physical (F.responseSplit e y R).1 := by
  rw [F.responseSplit_direction e he, ← map_smul, ← map_smul]
  unfold ExposureFrame.responseDirection
  rw [norm_smul_unitQueryDirection]
  rfl

end RandomizedFO2003.Rotations
