import NCConcave16991.DenseSmoothGeometry
import Mathlib.Analysis.Calculus.Gradient.Basic

/-! # Actual individual smoothness, independent of stage count and dimension -/

noncomputable section

namespace NCConcave16991.DenseSmooth

open ConeSmooth Set
open scoped ContDiff InnerProductSpace BigOperators

set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 4

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {n T : ℕ}

def smoothnessConstant : ℝ := 2000 * (1 + densitySlopeBound)

theorem smoothnessConstant_pos : 0 < smoothnessConstant := by
  have hh := densitySlopeBound_nonneg
  unfold smoothnessConstant
  positivity

theorem quadratic_fderiv (x : Blocks E T) :
    fderiv ℝ (fun z : Blocks E T ↦ (33 / 32 : ℝ) * ‖z‖ ^ 2) x =
      (33 / 16 : ℝ) • innerSL ℝ x := by
  have hh := (((hasFDerivAt_id x).norm_sq).const_mul (33 / 32 : ℝ)).fderiv
  simp only [id_eq] at hh
  rw [hh]
  ext h
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    innerSL_apply_apply, id_eq, smul_eq_mul, two_smul]
  ring

theorem quadratic_hessian_bound (x : Blocks E T) :
    ‖fderiv ℝ (fderiv ℝ (fun z : Blocks E T ↦ (33 / 32 : ℝ) * ‖z‖ ^ 2)) x‖ ≤ 33 / 16 := by
  apply norm_fderiv_le_of_lip' (𝕜 := ℝ) (by norm_num)
  exact Filter.Eventually.of_forall (fun y ↦ by
    rw [quadratic_fderiv, quadratic_fderiv, ← smul_sub, ← map_sub,
      norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 33 / 16), innerSL_apply_norm])

theorem componentChain_hessian_bound {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (u : Fin (T + 1) → E) (hu : ∀ j, ‖u j‖ = 1)
    (rows : Fin n → Fin (T + 1) → E) (hr : ∀ i j, ‖rows i j‖ = 1)
    (i : Fin n) (x : Blocks E T) :
    ‖fderiv ℝ (fderiv ℝ (componentChain ρ u rows i)) x‖ ≤ smoothnessConstant / ρ := by
  let g : Fin (T + 1) → Pair E → ℝ := fun j ↦
    localCore (decide (j.val = 0)) ρ (previousDirection u j) (rows i j)
  have hg (j : Fin (T + 1)) : ContDiff ℝ 2 (g j) :=
    (localCore_contDiff _ _ _ _).of_le (by simp)
  have hsum : ‖fderiv ℝ (fderiv ℝ (fun z : Blocks E T ↦ ∑ j, g j (stageProjection j z))) x‖ ≤
      (500 * (1 + densitySlopeBound) / ρ) * 2 :=
    hessian_linear_family_bound g hg stageProjection
      (div_nonneg (mul_nonneg (by norm_num) (by linarith [densitySlopeBound_nonneg])) hρ.le) (by norm_num) x
      (fun j ↦ localCore_hessian_bound _ hρ hρ1 _ _ (previousDirection_unit u hu j) (hr i j) _)
      stageProjection_energy
  rw [componentChain_eq_stages]
  change ‖fderiv ℝ (fderiv ℝ (fun z : Blocks E T ↦
    (∑ j, g j (stageProjection j z)) + (33 / 32 : ℝ) * ‖z‖ ^ 2)) x‖ ≤ _
  have hS : ContDiff ℝ 2 (fun z : Blocks E T ↦ ∑ j, g j (stageProjection j z)) :=
    ContDiff.sum (fun j _ ↦ (hg j).comp
      (show ContDiff ℝ 2 (stageProjection (E := E) (T := T) j) from
        (stageProjection (E := E) (T := T) j).contDiff))
  have hQ : ContDiff ℝ 2 (fun z : Blocks E T ↦ (33 / 32 : ℝ) * ‖z‖ ^ 2) :=
    contDiff_const.mul (contDiff_norm_sq ℝ)
  rw [hessian_add _ _ hS hQ]
  have ht := norm_add_le
    (fderiv ℝ (fderiv ℝ (fun z : Blocks E T ↦ ∑ j, g j (stageProjection j z))) x)
    (fderiv ℝ (fderiv ℝ (fun z : Blocks E T ↦ (33 / 32 : ℝ) * ‖z‖ ^ 2)) x)
  apply ht.trans ((add_le_add hsum (quadratic_hessian_bound x)).trans _)
  apply (le_div_iff₀ hρ).mpr
  have he : (500 * (1 + densitySlopeBound) / ρ * 2 + (33 / 16 : ℝ)) * ρ =
      1000 * (1 + densitySlopeBound) + (33 / 16 : ℝ) * ρ := by
    field_simp
    ring
  rw [he]
  unfold smoothnessConstant
  nlinarith [densitySlopeBound_nonneg]

theorem componentChain_fderiv_sub_bound {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (u : Fin (T + 1) → E) (hu : ∀ j, ‖u j‖ = 1)
    (rows : Fin n → Fin (T + 1) → E) (hr : ∀ i j, ‖rows i j‖ = 1)
    (i : Fin n) (x y : Blocks E T) :
    ‖fderiv ℝ (componentChain ρ u rows i) x - fderiv ℝ (componentChain ρ u rows i) y‖ ≤
      (smoothnessConstant / ρ) * ‖x - y‖ := by
  have hs := componentChain_contDiff ρ u rows i
  have hd : Differentiable ℝ (fderiv ℝ (componentChain ρ u rows i)) :=
    (hs.fderiv_right (m := 1) (by simp)).differentiable one_ne_zero
  exact Convex.norm_image_sub_le_of_norm_fderiv_le (s := univ) (𝕜 := ℝ)
    (f := fderiv ℝ (componentChain ρ u rows i)) (fun z _ ↦ hd z)
    (fun z _ ↦ componentChain_hessian_bound hρ hρ1 u hu rows hr i z) convex_univ (mem_univ y) (mem_univ x)

theorem componentChain_gradient_sub_bound {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (u : Fin (T + 1) → E) (hu : ∀ j, ‖u j‖ = 1)
    (rows : Fin n → Fin (T + 1) → E) (hr : ∀ i j, ‖rows i j‖ = 1)
    (i : Fin n) (x y : Blocks E T) :
    ‖gradient (componentChain ρ u rows i) x - gradient (componentChain ρ u rows i) y‖ ≤
      (smoothnessConstant / ρ) * ‖x - y‖ := by
  rw [← (InnerProductSpace.toDual ℝ (Blocks E T)).norm_map, map_sub, toDual_gradient, toDual_gradient]
  exact componentChain_fderiv_sub_bound hρ hρ1 u hu rows hr i x y

end NCConcave16991.DenseSmooth
