import NCConcave16991.GlobalHardStageCalculus
import Mathlib.Analysis.Calculus.Gradient.Basic

/-! # Actual global gradient bound for the source state penalty -/

namespace NCConcave16991.GlobalHard

noncomputable section

open Set LocalizationRadial LocalizationHessian
open scoped InnerProductSpace

theorem scalar_derivative_sub_bound (g g' : ℝ → ℝ) (C : ℝ)
    (hg : ∀ t, HasDerivAt g (g' t) t) (hb : ∀ t, |g' t| ≤ C) (x y : ℝ) :
    |g x - g y| ≤ C * |x - y| := by
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le (s := univ) (𝕜 := ℝ)
    (f := g) (fun t _ ↦ (hg t).differentiableAt)
    (fun t _ ↦ by simpa only [(hg t).deriv, Real.norm_eq_abs] using hb t)
    convex_univ (mem_univ y) (mem_univ x)
  simpa only [Real.norm_eq_abs] using hh

theorem activationSqDerivative_sub_bound (x y : ℝ) :
    |activationSqDerivative x - activationSqDerivative y| ≤ 1666 * |x - y| :=
  scalar_derivative_sub_bound _ _ _ activationSqDerivative_hasDerivAt activationSqSecond_abs_bound x y

theorem statePotentialDerivative_abs_bound (t : ℝ) : |statePotentialDerivative t| ≤ radialSlope := by
  rw [abs_le]
  exact ⟨(statePotentialDerivative_bounds t).1,
    (statePotentialDerivative_bounds t).2.trans (by norm_num [radialSlope])⟩

theorem statePotentialDerivative_sub_bound (x y : ℝ) :
    |statePotentialDerivative x - statePotentialDerivative y| ≤ (160 * radialSlope) * |x - y| :=
  scalar_derivative_sub_bound _ _ _ statePotentialDerivative_hasDerivAt statePotentialSecond_abs_bound x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem scalar_score_fderiv (g g' : ℝ → ℝ) (hg : ∀ t, HasDerivAt g (g' t) t) (v s : E) :
    fderiv ℝ (fun z ↦ g (stateScore v z)) s = g' (stateScore v s) • fderiv ℝ (stateScore v) s := by
  exact ((hg (stateScore v s)).comp_hasFDerivAt s
    ((stateScore_contDiff v).differentiable (by simp) s).hasFDerivAt).fderiv

/-- A direct chain-rule estimate on the actual capped score, with the scalar
derivative bounded only on its actual image. -/
theorem scalar_score_fderiv_sub_bound (g g' : ℝ → ℝ) (hg : ∀ t, HasDerivAt g (g' t) t)
    (D C : ℝ) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hfirst : ∀ t, |t| ≤ 20 → |g' t| ≤ D)
    (hsecond : ∀ x y, |g' x - g' y| ≤ C * |x - y|)
    (v : E) (hv : ‖v‖ = 1) (x y : E) :
    ‖fderiv ℝ (fun z ↦ g (stateScore v z)) x - fderiv ℝ (fun z ↦ g (stateScore v z)) y‖ ≤
      (C + 2 * D) * ‖x - y‖ := by
  rw [scalar_score_fderiv g g' hg, scalar_score_fderiv g g' hg]
  have he : g' (stateScore v x) • fderiv ℝ (stateScore v) x -
      g' (stateScore v y) • fderiv ℝ (stateScore v) y =
      (g' (stateScore v x) - g' (stateScore v y)) • fderiv ℝ (stateScore v) x +
      g' (stateScore v y) • (fderiv ℝ (stateScore v) x - fderiv ℝ (stateScore v) y) := by
    simp only [sub_smul, smul_sub]
    abel
  rw [he]
  have htri := norm_add_le
    ((g' (stateScore v x) - g' (stateScore v y)) • fderiv ℝ (stateScore v) x)
    (g' (stateScore v y) • (fderiv ℝ (stateScore v) x - fderiv ℝ (stateScore v) y))
  simp only [norm_smul, Real.norm_eq_abs] at htri
  have hs : |stateScore v x - stateScore v y| ≤ ‖x - y‖ :=
    radialCap_score_lipschitz (by norm_num : (0 : ℝ) < 10) v hv x y
  have hd : ‖fderiv ℝ (stateScore v) x‖ ≤ 1 := radialScore_fderiv_norm_le (by norm_num) v hv x
  have hdx : ‖fderiv ℝ (stateScore v) x - fderiv ℝ (stateScore v) y‖ ≤ 2 * ‖x - y‖ :=
    (radialScore_fderiv_sub_bound (by norm_num : (0 : ℝ) < 10) v hv x y).trans
      (mul_le_mul_of_nonneg_right (by norm_num : (14 : ℝ) / 10 ≤ 2) (norm_nonneg _))
  have hc := (hsecond (stateScore v x) (stateScore v y)).trans (mul_le_mul_of_nonneg_left hs hC)
  have hf := hfirst (stateScore v y) (stateScore_cap_bound v hv y)
  have hterm1 := mul_le_mul hc hd (norm_nonneg _) (mul_nonneg hC (norm_nonneg (x - y)))
  have hterm2 := mul_le_mul hf hdx (norm_nonneg _) hD
  nlinarith

theorem activationSq_score_fderiv_sub_bound (v : E) (hv : ‖v‖ = 1) (x y : E) :
    ‖fderiv ℝ (fun z ↦ activationSq (stateScore v z)) x -
      fderiv ℝ (fun z ↦ activationSq (stateScore v z)) y‖ ≤ 3026 * ‖x - y‖ := by
  have hfirst (t : ℝ) (ht : |t| ≤ 20) : |activationSqDerivative t| ≤ 680 :=
    (activationSqDerivative_bound t).trans (by nlinarith)
  have hh := scalar_score_fderiv_sub_bound activationSq activationSqDerivative activationSq_hasDerivAt
    680 1666 (by norm_num) (by norm_num) hfirst activationSqDerivative_sub_bound v hv x y
  norm_num at hh
  exact hh

theorem statePotential_score_fderiv_sub_bound (v : E) (hv : ‖v‖ = 1) (x y : E) :
    ‖fderiv ℝ (fun z ↦ statePotential (stateScore v z)) x -
      fderiv ℝ (fun z ↦ statePotential (stateScore v z)) y‖ ≤ 5251554 * ‖x - y‖ := by
  convert scalar_score_fderiv_sub_bound statePotential statePotentialDerivative statePotential_hasDerivAt
    radialSlope (160 * radialSlope) (by norm_num [radialSlope]) (by norm_num [radialSlope])
    (fun t _ ↦ statePotentialDerivative_abs_bound t) statePotentialDerivative_sub_bound v hv x y using 1 <;>
    norm_num [radialSlope]

theorem statePenalty_fderiv (v s : E) : fderiv ℝ (statePenalty v) s =
    (gamma / 2) • (2 • innerSL ℝ s) -
      (gamma / 2) • fderiv ℝ (fun z ↦ activationSq (stateScore v z)) s +
        fderiv ℝ (fun z ↦ statePotential (stateScore v z)) s := by
  have hn := (hasStrictFDerivAt_norm_sq s).hasFDerivAt.const_mul (gamma / 2)
  have hh := ((activationSq_contDiff.comp (stateScore_contDiff v)).differentiable (by simp) s).hasFDerivAt.const_mul (gamma / 2)
  have hp := ((statePotential_contDiff.comp (stateScore_contDiff v)).differentiable (by simp) s).hasFDerivAt
  exact ((hn.sub hh).add hp).fderiv

/-- The full source state penalty has the explicit global constant in E.14,
derived from its actual gradient and the actual cutoffs. -/
theorem statePenalty_fderiv_sub_bound (v : E) (hv : ‖v‖ = 1) (x y : E) :
    ‖fderiv ℝ (statePenalty v) x - fderiv ℝ (statePenalty v) y‖ ≤ 11761754 * ‖x - y‖ := by
  rw [statePenalty_fderiv, statePenalty_fderiv]
  have he : (gamma / 2) • (2 • innerSL ℝ x) -
      (gamma / 2) • fderiv ℝ (fun z ↦ activationSq (stateScore v z)) x +
        fderiv ℝ (fun z ↦ statePotential (stateScore v z)) x -
      ((gamma / 2) • (2 • innerSL ℝ y) -
        (gamma / 2) • fderiv ℝ (fun z ↦ activationSq (stateScore v z)) y +
          fderiv ℝ (fun z ↦ statePotential (stateScore v z)) y) =
      gamma • innerSL ℝ (x - y) -
        (gamma / 2) • (fderiv ℝ (fun z ↦ activationSq (stateScore v z)) x -
          fderiv ℝ (fun z ↦ activationSq (stateScore v z)) y) +
        (fderiv ℝ (fun z ↦ statePotential (stateScore v z)) x -
          fderiv ℝ (fun z ↦ statePotential (stateScore v z)) y) := by
    simp only [map_sub, smul_sub]
    module
  rw [he]
  let H := fderiv ℝ (fun z ↦ activationSq (stateScore v z)) x -
    fderiv ℝ (fun z ↦ activationSq (stateScore v z)) y
  let P := fderiv ℝ (fun z ↦ statePotential (stateScore v z)) x -
    fderiv ℝ (fun z ↦ statePotential (stateScore v z)) y
  have htri : ‖gamma • innerSL ℝ (x - y) - (gamma / 2) • H + P‖ ≤
      ‖gamma • innerSL ℝ (x - y)‖ + ‖(gamma / 2) • H‖ + ‖P‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  simp only [norm_smul, innerSL_apply_norm, Real.norm_eq_abs] at htri
  have hh := activationSq_score_fderiv_sub_bound v hv x y
  have hp := statePotential_score_fderiv_sub_bound v hv x y
  norm_num [gamma, H, P] at htri ⊢
  nlinarith

variable [CompleteSpace E]

theorem statePenalty_gradient_sub_bound (v : E) (hv : ‖v‖ = 1) (x y : E) :
    ‖gradient (statePenalty v) x - gradient (statePenalty v) y‖ ≤ 11761754 * ‖x - y‖ := by
  have he : ‖gradient (statePenalty v) x - gradient (statePenalty v) y‖ =
      ‖fderiv ℝ (statePenalty v) x - fderiv ℝ (statePenalty v) y‖ := by
    rw [← (InnerProductSpace.toDual ℝ E).norm_map, map_sub, toDual_gradient, toDual_gradient]
  rw [he]
  exact statePenalty_fderiv_sub_bound v hv x y

end

end NCConcave16991.GlobalHard
