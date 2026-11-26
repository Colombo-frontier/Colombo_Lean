import GradientHessian.LocalizedBounds
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.Compact

/-! Actual minimizers used in the adjacent-level folding appendix.
Connecting their local sum to the full hierarchical objective is a separate theorem.
-/

noncomputable section

namespace GradientHessian.Localized

open Filter Bornology
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem drive_gradient_norm_lt {w : ℝ} (hw : 0 < w) (c u : E) :
    ‖gradient (drive w c) u‖ < 16 := by
  rw [(drive_hasGradientAt hw c u).gradient, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ 16 / Real.sqrt (w ^ 2 + ‖u - c‖ ^ 2))]
  have hp : 0 < Real.sqrt (w ^ 2 + ‖u - c‖ ^ 2) := by positivity
  have hs := Real.sq_sqrt (by positivity : 0 ≤ w ^ 2 + ‖u - c‖ ^ 2)
  have hlt : ‖u - c‖ < Real.sqrt (w ^ 2 + ‖u - c‖ ^ 2) := by
    apply (sq_lt_sq₀ (norm_nonneg _) hp.le).1
    rw [hs]
    nlinarith
  rw [div_mul_eq_mul_div, div_lt_iff₀ hp]
  nlinarith

theorem publicPotential_hasGradientAt {R : ℝ} (hR : 0 < R) (u : E) :
    HasGradientAt (publicPotential R)
      ((16 / Real.sqrt (R ^ 2 + ‖u‖ ^ 2)) • u) u := by
  have h := (drive_hasGradientAt hR (0 : E) u).hasFDerivAt.sub_const (16 * R)
  have heq : publicPotential R = (fun x : E => drive R 0 x - 16 * R) := by
    funext x
    simp [drive, publicPotential, mul_sub]
  rw [hasGradientAt_iff_hasFDerivAt, heq]
  simpa only [sub_zero] using h

theorem publicPotential_gradient_norm_lt {R : ℝ} (hR : 0 < R) (u : E) :
    ‖gradient (publicPotential R) u‖ < 16 := by
  rw [(publicPotential_hasGradientAt hR u).gradient]
  have h := drive_gradient_norm_lt hR (0 : E) u
  rw [(drive_hasGradientAt hR (0 : E) u).gradient] at h
  simpa only [sub_zero] using h

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem well_continuous (R w : ℝ) (a : E) : Continuous (well R w a) := by
  unfold well
  fun_prop

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem well_add_coercive {w : ℝ} (hw : 0 < w) (R : ℝ) (a : E)
    {h : E → ℝ} (hh : ∀ u, 0 ≤ h u) :
    Tendsto (fun u => well R w a u + h u) (cobounded E) atTop := by
  apply tendsto_atTop.2
  intro b
  let K := publicPotential R a - 160 * w
  filter_upwards [eventually_cobounded_le_norm (E := E)
    (‖a‖ + 1 + (b - K) * w / 8)] with u hu
  have hdist : ‖u‖ ≤ ‖u - a‖ + ‖a‖ := by
    simpa only [sub_add_cancel] using norm_add_le (u - a) a
  have ht : ‖u - a‖ ≤ ‖u - a‖ ^ 2 + 1 := by nlinarith [sq_nonneg (‖u - a‖ - 1)]
  have hs : (b - K) * w / 8 ≤ ‖u - a‖ ^ 2 := by linarith
  have hl : b - K ≤ 8 / w * ‖u - a‖ ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hw]
    have hs' := (div_le_iff₀ (by norm_num : (0 : ℝ) < 8)).1 hs
    nlinarith only [hs']
  have hn := hh u
  dsimp [K] at hl
  unfold well
  linarith

theorem well_add_hasGradientAt (R w : ℝ) (a u : E) {h : E → ℝ} {g : E}
    (hh : HasGradientAt h g u) :
    HasGradientAt (fun v => well R w a v + h v) ((16 / w) • (u - a) + g) u := by
  rw [hasGradientAt_iff_hasFDerivAt]
  simpa only [map_add] using (well_hasGradientAt R w a u).hasFDerivAt.add hh.hasFDerivAt

variable [ProperSpace E]

/-- A nonnegative smooth perturbation with gradient norm below 16 has a well-plus-perturbation
minimizer strictly inside the completion ball. All assumptions are instantiated below. -/
theorem exists_well_add_minimizer {w : ℝ} (hw : 0 < w) (R : ℝ) (a : E)
    {h : E → ℝ} (hc : Continuous h) (hd : Differentiable ℝ h)
    (hn : ∀ u, 0 ≤ h u) (hg : ∀ u, ‖gradient h u‖ < 16) :
    ∃ u : E, (∀ v, well R w a u + h u ≤ well R w a v + h v) ∧
      HasGradientAt (fun v => well R w a v + h v) 0 u ∧ ‖u - a‖ < w := by
  have hco : Tendsto (fun u => well R w a u + h u) (cocompact E) atTop := by
    rw [← Metric.cobounded_eq_cocompact]
    exact well_add_coercive hw R a hn
  obtain ⟨u, hu⟩ := ((well_continuous R w a).add hc).exists_forall_le hco
  have hmin : IsLocalMin (fun u => well R w a u + h u) u := Filter.Eventually.of_forall hu
  have hgrad := well_add_hasGradientAt R w a u (hd u).hasGradientAt
  have hzero : (16 / w) • (u - a) + gradient h u = 0 := by
    apply (InnerProductSpace.toDual ℝ E).injective
    simpa using hmin.hasFDerivAt_eq_zero hgrad.hasFDerivAt
  have hnorm := congrArg norm (eq_neg_of_add_eq_zero_left hzero)
  rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 16 / w)] at hnorm
  have hlt : 16 / w * ‖u - a‖ < 16 := by rw [hnorm]; exact hg u
  rw [div_mul_eq_mul_div, div_lt_iff₀ hw] at hlt
  refine ⟨u, hu, ?_, ?_⟩
  · simpa only [hzero] using hgrad
  · nlinarith

/-- The minimizer for the first folded parent coordinate, using the actual drive potential. -/
theorem exists_well_drive_minimizer {w W : ℝ} (hw : 0 < w) (hW : 0 < W)
    (R : ℝ) (a b : E) :
    ∃ u : E, (∀ v, well R w a u + drive W b u ≤ well R w a v + drive W b v) ∧
      HasGradientAt (fun v => well R w a v + drive W b v) 0 u ∧ ‖u - a‖ < w := by
  apply exists_well_add_minimizer hw R a (drive_contDiff hW b 1).continuous
    (fun u => (drive_hasGradientAt hW b u).differentiableAt)
  · intro u
    unfold drive
    positivity
  · exact drive_gradient_norm_lt hW b

/-- The minimizers for the other seven folded parent coordinates. -/
theorem exists_well_public_minimizer {w P : ℝ} (hw : 0 < w) (hP : 0 < P)
    (R : ℝ) (a : E) :
    ∃ u : E, (∀ v, well R w a u + publicPotential P u ≤
      well R w a v + publicPotential P v) ∧
      HasGradientAt (fun v => well R w a v + publicPotential P v) 0 u ∧ ‖u - a‖ < w := by
  exact exists_well_add_minimizer hw R a (publicPotential_contDiff hP 1).continuous
    (fun u => (publicPotential_hasGradientAt hP u).differentiableAt)
    (publicPotential_nonneg hP.le) (publicPotential_gradient_norm_lt hP)

end GradientHessian.Localized
