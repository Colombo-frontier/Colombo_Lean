import NoisyZO.SmoothDescent
import NoisyZO.HardCenterGeometry

/-!
# Quantitative perturbations of the base quadratic

The hard objective is the sum of `‖x‖²` and a smooth localized perturbation.
A unit Lipschitz bound on the perturbation gradient simultaneously implies
one-strong convexity of the objective and three-Lipschitzness of its gradient.
This packages the analytic argument from Appendix A independently of the
remaining high-order profile estimate.
-/

open scoped ContDiff Gradient InnerProductSpace

namespace NoisyZO

noncomputable section

/-- The localized nonquadratic part of a hard-family objective. -/
def hardPerturbation {d : ℕ} (cutoff : Point d → ℝ) (rho : ℝ)
    (s : Fin d → ℝ) (x : Point d) : ℝ :=
  -rho * signedSum s x * cutoff x

theorem hardValue_eq_norm_sq_add_hardPerturbation
    {d : ℕ} (cutoff : Point d → ℝ) (rho : ℝ)
    (s : Fin d → ℝ) (x : Point d) :
    hardValue cutoff rho s x = ‖x‖ ^ 2 + hardPerturbation cutoff rho s x := by
  unfold hardValue hardPerturbation
  ring

theorem hardPerturbation_radialCutoff_contDiff
    {d : ℕ} (c h : ℝ) (hh : 0 < h) (s : Fin d → ℝ) {n : ℕ∞} :
    ContDiff ℝ n
      (hardPerturbation (radialCutoff d h hh) c s) := by
  unfold hardPerturbation
  apply (contDiff_const.mul ?_).mul (radialCutoff_contDiff d h hh)
  unfold signedSum
  fun_prop

theorem gradient_norm_sq (d : ℕ) (x : Point d) :
    ∇ (fun z : Point d ↦ ‖z‖ ^ 2) x = (2 : ℝ) • x := by
  apply ext_inner_right ℝ
  intro z
  rw [inner_gradient_left, fderiv_norm_sq_apply]
  simp only [smul_apply]
  rw [real_inner_smul_left]
  simp

/-- Every positive-order iterated derivative of a continuous linear map is
independent of the base point.  At order one it is the map itself; at all
higher orders it vanishes. -/
theorem iteratedFDeriv_continuousLinearMap_eq_of_pos
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) {n : ℕ} (hn : 0 < n) (x y : E) :
    iteratedFDeriv ℝ n L x = iteratedFDeriv ℝ n L y := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [iteratedFDeriv_succ_eq_comp_right,
    iteratedFDeriv_succ_eq_comp_right]
  simp only [Function.comp_apply, ContinuousLinearMap.fderiv]
  by_cases hm : m = 0
  · subst m
    rfl
  · have hxzero : iteratedFDeriv ℝ m (fun _ : E ↦ L) x = 0 :=
      congrFun (iteratedFDeriv_const_of_ne (𝕜 := ℝ) (E := E) hm L) x
    have hyzero : iteratedFDeriv ℝ m (fun _ : E ↦ L) y = 0 :=
      congrFun (iteratedFDeriv_const_of_ne (𝕜 := ℝ) (E := E) hm L) y
    change
      (continuousMultilinearCurryRightEquiv' ℝ m E F).symm
          (iteratedFDeriv ℝ m (fun _ : E ↦ L) x) =
        (continuousMultilinearCurryRightEquiv' ℝ m E F).symm
          (iteratedFDeriv ℝ m (fun _ : E ↦ L) y)
    rw [hxzero, hyzero]

/-- Starting at order two, every iterated derivative of `x ↦ ‖x‖²` is
independent of the base point. -/
theorem iteratedFDeriv_norm_sq_eq_of_two_le
    {d k : ℕ} (hk : 2 ≤ k) (x y : Point d) :
    iteratedFDeriv ℝ k (fun z : Point d ↦ ‖z‖ ^ 2) x =
      iteratedFDeriv ℝ k (fun z : Point d ↦ ‖z‖ ^ 2) y := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [show 2 + n = (n + 1) + 1 by omega,
    iteratedFDeriv_succ_eq_comp_right,
    iteratedFDeriv_succ_eq_comp_right]
  simp only [Function.comp_apply]
  rw [fderiv_norm_sq]
  let L : Point d →L[ℝ] Point d →L[ℝ] ℝ :=
    2 • (innerSL ℝ : Point d →L[ℝ] Point d →L[ℝ] ℝ)
  have hL : iteratedFDeriv ℝ (n + 1) L x =
      iteratedFDeriv ℝ (n + 1) L y :=
    iteratedFDeriv_continuousLinearMap_eq_of_pos L (by omega) x y
  change
    (continuousMultilinearCurryRightEquiv' ℝ (n + 1) (Point d) ℝ).symm
        (iteratedFDeriv ℝ (n + 1) L x) =
      (continuousMultilinearCurryRightEquiv' ℝ (n + 1) (Point d) ℝ).symm
        (iteratedFDeriv ℝ (n + 1) L y)
  rw [hL]

theorem gradient_add_of_contDiff_one
    {d : ℕ} {f g : Point d → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (x : Point d) :
    ∇ (fun z ↦ f z + g z) x = ∇ f x + ∇ g x := by
  apply ext_inner_right ℝ
  intro z
  simp only [inner_gradient_left, inner_add_left]
  change (fderiv ℝ (f + g) x) z =
    (fderiv ℝ f x) z + (fderiv ℝ g x) z
  rw [fderiv_add
    ((hf.differentiable one_ne_zero).differentiableAt)
    ((hg.differentiable one_ne_zero).differentiableAt),
    add_apply]

/-- Exact gradient decomposition into the base quadratic and perturbation. -/
theorem gradient_hardValue_eq_two_smul_add_perturbation
    {d : ℕ} (c h : ℝ) (hh : 0 < h) (s : Fin d → ℝ) (x : Point d) :
    ∇ (hardValue (radialCutoff d h hh) c s) x =
      (2 : ℝ) • x + ∇ (hardPerturbation (radialCutoff d h hh) c s) x := by
  rw [show hardValue (radialCutoff d h hh) c s =
      fun z : Point d ↦
        ‖z‖ ^ 2 + hardPerturbation (radialCutoff d h hh) c s z by
    funext z
    exact hardValue_eq_norm_sq_add_hardPerturbation _ _ _ _]
  have hnorm : ContDiff ℝ 1 (fun z : Point d ↦ ‖z‖ ^ 2) :=
    contDiff_norm_sq ℝ
  have hp : ContDiff ℝ 1
      (hardPerturbation (radialCutoff d h hh) c s) :=
    hardPerturbation_radialCutoff_contDiff c h hh s
  rw [gradient_add_of_contDiff_one hnorm hp, gradient_norm_sq]

/-- A unit-Lipschitz perturbation gradient makes the complete hard objective
gradient three-Lipschitz. -/
theorem hardValue_gradient_lipschitz_of_perturbation
    {d : ℕ} (c h : ℝ) (hh : 0 < h) (s : Fin d → ℝ)
    (hpert : ∀ x y,
      ‖∇ (hardPerturbation (radialCutoff d h hh) c s) x -
        ∇ (hardPerturbation (radialCutoff d h hh) c s) y‖ ≤ ‖x - y‖) :
    ∀ x y,
      ‖∇ (hardValue (radialCutoff d h hh) c s) x -
        ∇ (hardValue (radialCutoff d h hh) c s) y‖ ≤ 3 * ‖x - y‖ := by
  intro x y
  rw [gradient_hardValue_eq_two_smul_add_perturbation,
    gradient_hardValue_eq_two_smul_add_perturbation]
  let gx := ∇ (hardPerturbation (radialCutoff d h hh) c s) x
  let gy := ∇ (hardPerturbation (radialCutoff d h hh) c s) y
  calc
    ‖((2 : ℝ) • x + gx) - ((2 : ℝ) • y + gy)‖ =
        ‖(2 : ℝ) • (x - y) + (gx - gy)‖ := by
      congr 1
      module
    _ ≤ ‖(2 : ℝ) • (x - y)‖ + ‖gx - gy‖ := norm_add_le _ _
    _ = 2 * ‖x - y‖ + ‖gx - gy‖ := by
      rw [norm_smul]
      norm_num
    _ ≤ 2 * ‖x - y‖ + ‖x - y‖ := by
      have hg : ‖gx - gy‖ ≤ ‖x - y‖ := by
        simpa only [gx, gy] using hpert x y
      linarith
    _ = 3 * ‖x - y‖ := by ring

/-- A unit-Lipschitz perturbation gradient makes the complete hard objective
one-strongly convex in the exact first-order form used by the model. -/
theorem hardValue_strong_of_perturbation
    {d : ℕ} (c h : ℝ) (hh : 0 < h) (s : Fin d → ℝ)
    (hpert : ∀ x y,
      ‖∇ (hardPerturbation (radialCutoff d h hh) c s) x -
        ∇ (hardPerturbation (radialCutoff d h hh) c s) y‖ ≤ ‖x - y‖) :
    ∀ x y,
      hardValue (radialCutoff d h hh) c s x +
        ⟪∇ (hardValue (radialCutoff d h hh) c s) x, y - x⟫_ℝ +
        (1 / 2 : ℝ) * ‖y - x‖ ^ 2 ≤
          hardValue (radialCutoff d h hh) c s y := by
  intro x y
  let p := hardPerturbation (radialCutoff d h hh) c s
  have hpSmooth : ContDiff ℝ 1 p :=
    hardPerturbation_radialCutoff_contDiff c h hh s
  have hpLower := firstOrderTaylor_lower_of_gradient_lipschitz
    p hpSmooth 1 (by norm_num) (by simpa only [one_mul] using hpert) x y
  have hquad := norm_add_sq_real x (y - x)
  have hxy : x + (y - x) = y := by abel
  rw [hxy] at hquad
  rw [gradient_hardValue_eq_two_smul_add_perturbation]
  rw [hardValue_eq_norm_sq_add_hardPerturbation,
    hardValue_eq_norm_sq_add_hardPerturbation,
    inner_add_left]
  rw [real_inner_smul_left]
  dsimp only [p] at hpLower ⊢
  nlinarith

/-- For derivative orders at least two, the Hölder increment of the complete
hard objective is exactly the increment of its localized perturbation. -/
theorem hardValue_higher_holder_of_perturbation
    {d k : ℕ} (hk : 2 ≤ k) (alpha c h : ℝ) (hh : 0 < h)
    (s : Fin d → ℝ)
    (hpert : ∀ x y,
      ‖iteratedFDeriv ℝ k
          (hardPerturbation (radialCutoff d h hh) c s) x -
        iteratedFDeriv ℝ k
          (hardPerturbation (radialCutoff d h hh) c s) y‖ ≤
        ‖x - y‖ ^ alpha) :
    ∀ x y,
      ‖iteratedFDeriv ℝ k
          (hardValue (radialCutoff d h hh) c s) x -
        iteratedFDeriv ℝ k
          (hardValue (radialCutoff d h hh) c s) y‖ ≤
        ‖x - y‖ ^ alpha := by
  intro x y
  let q : Point d → ℝ := fun z ↦ ‖z‖ ^ 2
  let p := hardPerturbation (radialCutoff d h hh) c s
  have hq : ContDiff ℝ k q := contDiff_norm_sq ℝ
  have hp : ContDiff ℝ k p :=
    hardPerturbation_radialCutoff_contDiff c h hh s
  have hqxqy : iteratedFDeriv ℝ k q x = iteratedFDeriv ℝ k q y :=
    iteratedFDeriv_norm_sq_eq_of_two_le hk x y
  rw [show hardValue (radialCutoff d h hh) c s = q + p by
      funext z
      exact hardValue_eq_norm_sq_add_hardPerturbation _ _ _ _,
    iteratedFDeriv_add_apply hq.contDiffAt hp.contDiffAt,
    iteratedFDeriv_add_apply hq.contDiffAt hp.contDiffAt,
    hqxqy, add_sub_add_left_eq_sub]
  exact hpert x y

end

end NoisyZO
