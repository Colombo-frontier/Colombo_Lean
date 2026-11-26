import GradientHessian.Localized
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded

/-! Actual value bounds and coercivity for the localized completion block.
The quantitative bounds on second and third derivatives are separate obligations.
-/

noncomputable section

namespace GradientHessian.Localized

open Filter Bornology
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E]

theorem sqrt_sq_add_sq_lower_left {a b : ℝ} (ha : 0 ≤ a) :
    a ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
  apply (sq_le_sq₀ ha (Real.sqrt_nonneg _)).1
  rw [Real.sq_sqrt (by positivity)]
  nlinarith [sq_nonneg b]

theorem sqrt_sq_add_sq_lower_right {a b : ℝ} (hb : 0 ≤ b) :
    b ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
  simpa [add_comm] using (sqrt_sq_add_sq_lower_left (b := a) hb)

theorem sqrt_sq_add_sq_upper {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a ^ 2 + b ^ 2) ≤ a + b := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).1
  rw [Real.sq_sqrt (by positivity)]
  nlinarith

theorem publicPotential_nonneg {R : ℝ} (hR : 0 ≤ R) (u : E) :
    0 ≤ publicPotential R u := by
  have h := sqrt_sq_add_sq_lower_left (b := ‖u‖) hR
  unfold publicPotential
  linarith

theorem publicPotential_zero {R : ℝ} (hR : 0 ≤ R) : publicPotential R (0 : E) = 0 := by
  simp [publicPotential, Real.sqrt_sq hR]

theorem publicPotential_lower (R : ℝ) (u : E) :
    16 * (‖u‖ - R) ≤ publicPotential R u := by
  have h := sqrt_sq_add_sq_lower_right (a := R) (norm_nonneg u)
  unfold publicPotential
  linarith

theorem publicPotential_upper {R : ℝ} (hR : 0 ≤ R) (u : E) :
    publicPotential R u ≤ 16 * ‖u‖ := by
  have h := sqrt_sq_add_sq_upper hR (norm_nonneg u)
  unfold publicPotential
  linarith

theorem drive_lower (w : ℝ) (c u : E) : 16 * ‖u - c‖ ≤ drive w c u := by
  have h := sqrt_sq_add_sq_lower_right (a := w) (norm_nonneg (u - c))
  unfold drive
  linarith

theorem drive_upper {w : ℝ} (hw : 0 ≤ w) (c u : E) :
    drive w c u ≤ 16 * (w + ‖u - c‖) := by
  have h := sqrt_sq_add_sq_upper hw (norm_nonneg (u - c))
  unfold drive
  linarith

theorem cutoff_bounds (w : ℝ) (c u : E) : 0 ≤ cutoff w c u ∧ cutoff w c u ≤ 1 := by
  have h := Profiles.step_bounds ((‖u - c‖ ^ 2 - 4 * w ^ 2) / (5 * w ^ 2))
  unfold cutoff
  constructor <;> linarith

theorem publicPotential_coercive (R : ℝ) :
    Tendsto (publicPotential R : E → ℝ) (cobounded E) atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_cobounded_le_norm (E := E) (b / 16 + R)] with u hu
  have h := publicPotential_lower R u
  linarith

section Hilbert

variable [InnerProductSpace ℝ E] [CompleteSpace E]

theorem drive_fderiv_norm_le {w : ℝ} (hw : 0 < w) (c u : E) :
    ‖fderiv ℝ (drive w c) u‖ ≤ 16 := by
  rw [(drive_hasGradientAt hw c u).hasFDerivAt.fderiv]
  simp only [LinearIsometryEquiv.norm_map, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ 16 / Real.sqrt (w ^ 2 + ‖u - c‖ ^ 2))]
  have hp : 0 < Real.sqrt (w ^ 2 + ‖u - c‖ ^ 2) := by positivity
  have h := sqrt_sq_add_sq_lower_right (a := w) (norm_nonneg (u - c))
  rw [div_mul_eq_mul_div, div_le_iff₀ hp]
  nlinarith

theorem drive_lipschitz {w : ℝ} (hw : 0 < w) (c u v : E) :
    |drive w c u - drive w c v| ≤ 16 * ‖u - v‖ := by
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (f := drive w c) (s := Set.univ) (C := (16 : ℝ))
    (fun x _ => (drive_hasGradientAt hw c x).differentiableAt)
    (fun x _ => drive_fderiv_norm_le hw c x) (convex_univ : Convex ℝ (Set.univ : Set E))
    (Set.mem_univ v) (Set.mem_univ u)
  simpa only [Real.norm_eq_abs] using h

theorem publicPotential_lipschitz {R : ℝ} (hR : 0 < R) (u v : E) :
    |publicPotential R u - publicPotential R v| ≤ 16 * ‖u - v‖ := by
  have h := drive_lipschitz hR (0 : E) u v
  simpa [publicPotential, drive, mul_sub, sub_sub_sub_cancel_right] using h

/-- The well lies between -208 w and -40 w below the public baseline on its support. -/
theorem well_difference_bounds {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (c u : E)
    (hu : ‖u - c‖ ≤ 3 * w) :
    -208 * w ≤ well R w c u - publicPotential R u ∧
      well R w c u - publicPotential R u ≤ -40 * w := by
  have h := publicPotential_lipschitz hR u c
  have hl := (abs_le.mp h).1
  have hr := (abs_le.mp h).2
  have ht0 := norm_nonneg (u - c)
  have hs : ‖u - c‖ ^ 2 ≤ 9 * w ^ 2 := by nlinarith
  have hterm0 : 0 ≤ 8 / w * ‖u - c‖ ^ 2 := by positivity
  have hterm : 8 / w * ‖u - c‖ ^ 2 ≤ 72 * w := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hw]
    nlinarith
  unfold well
  constructor <;> nlinarith

/-- The global perturbation value bounds in equation (loc-values). -/
theorem perturbation_bounds {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (c u : E) :
    -208 * w ≤ perturbation R w c u ∧ perturbation R w c u ≤ 0 := by
  by_cases hu : ‖u - c‖ ≤ 3 * w
  · rcases well_difference_bounds hR hw c u hu with ⟨hlo, hhi⟩
    rcases cutoff_bounds w c u with ⟨hc0, hc1⟩
    have hn : well R w c u - publicPotential R u ≤ 0 := by linarith
    have hprod := mul_le_mul_of_nonpos_right hc1 hn
    unfold perturbation
    constructor
    · nlinarith
    · exact mul_nonpos_of_nonneg_of_nonpos hc0 hn
  · rw [perturbation_eq_zero_of_three_mul_le_norm hw (le_of_not_ge hu)]
    constructor <;> linarith

/-- Uniform bounds for the noncompact incoming coefficient B. -/
theorem incoming_bounds {R w : ℝ} (hw : 0 < w) (hscale : 16 * w ≤ R)
    (c u : E) (hc : ‖c‖ = R) :
    256 * R ≤ incoming R w c u ∧ incoming R w c u ≤ 768 * R := by
  have hR : 0 < R := by linarith
  rcases perturbation_bounds hR hw c u with ⟨hψlo, hψhi⟩
  have hPlo := publicPotential_lower R u
  have hPhi := publicPotential_upper hR.le u
  have hGlo := drive_lower w c u
  have hGhi := drive_upper hw.le c u
  have hnorm1 : ‖u‖ - ‖u - c‖ ≤ R := by
    simpa [hc] using norm_sub_norm_le u (u - c)
  have hnorm2 : ‖u - c‖ - ‖u‖ ≤ R := by
    have h := norm_sub_le u c
    rw [hc] at h
    linarith
  unfold incoming potential
  constructor <;> linarith

/-- Coercivity of the actual localized self potential, including its perturbation. -/
theorem potential_coercive {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (c : E) :
    Tendsto (potential R w c) (cobounded E) atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [(publicPotential_coercive R).eventually_ge_atTop (b + 208 * w)] with u hu
  have h := (perturbation_bounds hR hw c u).1
  unfold potential
  linarith

end Hilbert

end GradientHessian.Localized
