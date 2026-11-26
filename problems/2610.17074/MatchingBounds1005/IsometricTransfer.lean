import MatchingBounds1005.GradientLipschitz
import RandomizedFO2003.RotationGroup

/-! Transport of the actual objective and oracle under the same Euclidean
isometries and Haar rotations used by the geometry modules. -/
noncomputable section
open scoped InnerProductSpace ContDiff BigOperators

namespace MatchingBounds1005.IsometricTransfer
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def transport (U : E ≃ₗᵢ[ℝ] F) (f : E → ℝ) (y : F) : ℝ := f (U.symm y)

theorem smooth (U : E ≃ₗᵢ[ℝ] F) {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (transport U f) :=
  hf.comp U.symm.toContinuousLinearEquiv.contDiff

theorem hasGradientAt (U : E ≃ₗᵢ[ℝ] F) {f : E → ℝ} {g : E} {y : F}
    (hf : HasGradientAt f g (U.symm y)) : HasGradientAt (transport U f) (U g) y := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := hf.hasFDerivAt.comp y U.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
  convert h using 1
  ext v
  change ⟪U g, v⟫_ℝ = ⟪g, U.symm v⟫_ℝ
  exact U.inner_map_eq_flip g v

theorem gradient_eq (U : E ≃ₗᵢ[ℝ] F) {f : E → ℝ} (hf : Differentiable ℝ f) (y : F) :
    gradient (transport U f) y = U (gradient f (U.symm y)) :=
  (hasGradientAt U (hf (U.symm y)).hasGradientAt).gradient

theorem gradient_norm (U : E ≃ₗᵢ[ℝ] F) {f : E → ℝ} (hf : Differentiable ℝ f) (y : F) :
    ‖gradient (transport U f) y‖ = ‖gradient f (U.symm y)‖ := by
  rw [gradient_eq U hf, U.norm_map]

theorem radial_pairing (U : E ≃ₗᵢ[ℝ] F) {f : E → ℝ} (hf : Differentiable ℝ f) (y : F) :
    ⟪y, gradient (transport U f) y⟫_ℝ = ⟪U.symm y, gradient f (U.symm y)⟫_ℝ := by
  rw [gradient_eq U hf]
  simpa only [U.apply_symm_apply] using U.inner_map_map (U.symm y) (gradient f (U.symm y))

theorem readout (U : E ≃ₗᵢ[ℝ] F) (a : E) (y : F) :
    ⟪U a, y⟫_ℝ = ⟪a, U.symm y⟫_ℝ := U.inner_map_eq_flip a y

theorem gap (U : E ≃ₗᵢ[ℝ] F) (f : E → ℝ) (y : F) :
    transport U f 0 - transport U f y = f 0 - f (U.symm y) := by simp [transport]

theorem jet_norm_le (U : E ≃ₗᵢ[ℝ] F) {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (j : ℕ) (y : F) :
    ‖iteratedFDeriv ℝ j (transport U f) y‖ ≤ ‖iteratedFDeriv ℝ j f (U.symm y)‖ := by
  let P : F →L[ℝ] E := U.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hP : ‖P‖ ≤ 1 := by
    apply P.opNorm_le_bound (by norm_num)
    intro v
    change ‖U.symm v‖ ≤ 1 * ‖v‖
    rw [U.symm.norm_map, one_mul]
  have hlevel : (j : WithTop ℕ∞) ≤ ∞ :=
    by exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top)
  change ‖iteratedFDeriv ℝ j (f ∘ P) y‖ ≤ _
  rw [P.iteratedFDeriv_comp_right hf y hlevel]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j f (U.symm y)‖ * ‖P‖ ^ j := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ j f (U.symm y)).norm_compContinuousLinearMap_le (fun _ => P)
    _ ≤ ‖iteratedFDeriv ℝ j f (U.symm y)‖ * 1 :=
      mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg P) hP) (norm_nonneg _)
    _ = _ := mul_one _

theorem jet_norm (U : E ≃ₗᵢ[ℝ] F) {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (j : ℕ) (y : F) :
    ‖iteratedFDeriv ℝ j (transport U f) y‖ = ‖iteratedFDeriv ℝ j f (U.symm y)‖ := by
  apply le_antisymm (jet_norm_le U hf j y)
  have h := jet_norm_le U.symm (smooth U hf) j (U.symm y)
  have heq : transport U.symm (transport U f) = f := by
    funext x
    simp [transport]
  rw [heq] at h
  simpa only [LinearIsometryEquiv.symm_symm, U.apply_symm_apply] using h

section Rotation
variable [FiniteDimensional ℝ E]
open RandomizedFO2003.Rotations

def rotated (f : E → ℝ) (U : Rotation E) : E → ℝ := transport (isometry E U) f

theorem continuous_inverse_action :
    Continuous (fun p : Rotation E × E => (isometry E p.1).symm p.2) := by
  have h := (continuous_action E).comp (continuous_fst.inv.prodMk continuous_snd)
  simpa only [Function.comp_apply, isometry_inv] using h

theorem continuous_rotated {f : E → ℝ} (hf : Continuous f) :
    Continuous (fun p : Rotation E × E => rotated f p.1 p.2) :=
  hf.comp continuous_inverse_action

theorem continuous_rotated_gradient {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    Continuous (fun p : Rotation E × E => gradient (rotated f p.1) p.2) := by
  have hdf : Differentiable ℝ f := (contDiff_infty_iff_fderiv.mp hf).1
  have hg : Continuous (gradient f) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hf.continuous_fderiv (by simp))
  have heq : (fun p : Rotation E × E => gradient (rotated f p.1) p.2) =
      fun p => isometry E p.1 (gradient f ((isometry E p.1).symm p.2)) := by
    funext p
    exact gradient_eq (isometry E p.1) hdf p.2
  rw [heq]
  exact (continuous_action E).comp (continuous_fst.prodMk (hg.comp continuous_inverse_action))

/-- Joint continuity of the exact value-gradient oracle for one fixed Haar
rotation, suitable for the probability kernel measurability construction. -/
theorem continuous_rotated_oracle {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    Continuous (fun p : Rotation E × E => (rotated f p.1 p.2, gradient (rotated f p.1) p.2)) :=
  (continuous_rotated hf.continuous).prodMk (continuous_rotated_gradient hf)

end Rotation
end MatchingBounds1005.IsometricTransfer
