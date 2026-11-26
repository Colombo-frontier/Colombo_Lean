import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Tactic
import GradientHessian.Profiles

/-!
# Localized completion blocks from manuscript 2607 (2)

This module checks the literal scalar formulas, their global C3 regularity,
cancellation, actual gradients, and the complete localized activation and
one-sided robustness implications. It also checks the separation estimate
used in the adjacent-level folding appendix.
It does not assert that the complete hierarchy or oracle lower bound is proved.
-/

noncomputable section

namespace GradientHessian.Localized

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E]

/-- The manuscript's clamped septic profile. -/
abbrev step := Profiles.step

def publicPotential (R : ℝ) (u : E) : ℝ :=
  16 * (Real.sqrt (R ^ 2 + ‖u‖ ^ 2) - R)

def drive (w : ℝ) (c u : E) : ℝ :=
  16 * Real.sqrt (w ^ 2 + ‖u - c‖ ^ 2)

def well (R w : ℝ) (c u : E) : ℝ :=
  publicPotential R c - 160 * w + 8 / w * ‖u - c‖ ^ 2

def cutoff (w : ℝ) (c u : E) : ℝ :=
  1 - step ((‖u - c‖ ^ 2 - 4 * w ^ 2) / (5 * w ^ 2))

def perturbation (R w : ℝ) (c u : E) : ℝ :=
  cutoff w c u * (well R w c u - publicPotential R u)

def potential (R w : ℝ) (c u : E) : ℝ :=
  publicPotential R u + perturbation R w c u

def incoming (R w : ℝ) (c u : E) : ℝ :=
  potential R w c u - drive w c u + 512 * R

def port (w : ℝ) (c u : E) : ℝ :=
  1 - step ((‖u - c‖ ^ 2 - w ^ 2) / (3 * w ^ 2))

/-- Equation (loc-cancel), for the literal functions above. -/
theorem cancellation (R w : ℝ) (c u : E) :
    potential R w c u - incoming R w c u = drive w c u - 512 * R := by
  unfold incoming
  ring

theorem port_eq_one_of_norm_le {w : ℝ} {c u : E}
    (hw : 0 < w) (h : ‖u - c‖ ≤ w) : port w c u = 1 := by
  have hs : ‖u - c‖ ^ 2 - w ^ 2 ≤ 0 := by nlinarith [norm_nonneg (u - c)]
  have hd : (‖u - c‖ ^ 2 - w ^ 2) / (3 * w ^ 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hs (by positivity)
  simp [port, Profiles.step_nonpos hd]

theorem port_eq_zero_of_two_mul_le_norm {w : ℝ} {c u : E}
    (hw : 0 < w) (h : 2 * w ≤ ‖u - c‖) : port w c u = 0 := by
  have hden : 0 < 3 * w ^ 2 := by positivity
  have hs : 1 ≤ (‖u - c‖ ^ 2 - w ^ 2) / (3 * w ^ 2) := by
    rw [le_div_iff₀ hden]
    nlinarith [norm_nonneg (u - c)]
  simp [port, Profiles.step_ge_one hs]

theorem cutoff_eq_one_of_norm_le_two_mul {w : ℝ} {c u : E}
    (hw : 0 < w) (h : ‖u - c‖ ≤ 2 * w) : cutoff w c u = 1 := by
  have hs : ‖u - c‖ ^ 2 - 4 * w ^ 2 ≤ 0 := by nlinarith [norm_nonneg (u - c)]
  have hd : (‖u - c‖ ^ 2 - 4 * w ^ 2) / (5 * w ^ 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hs (by positivity)
  simp [cutoff, Profiles.step_nonpos hd]

theorem potential_eq_well_of_norm_le_two_mul {R w : ℝ} {c u : E}
    (hw : 0 < w) (h : ‖u - c‖ ≤ 2 * w) :
    potential R w c u = well R w c u := by
  simp [potential, perturbation, cutoff_eq_one_of_norm_le_two_mul hw h]

theorem perturbation_eq_zero_of_three_mul_le_norm {R w : ℝ} {c u : E}
    (hw : 0 < w) (h : 3 * w ≤ ‖u - c‖) : perturbation R w c u = 0 := by
  have hden : 0 < 5 * w ^ 2 := by positivity
  have hs : 1 ≤ (‖u - c‖ ^ 2 - 4 * w ^ 2) / (5 * w ^ 2) := by
    rw [le_div_iff₀ hden]
    nlinarith [norm_nonneg (u - c)]
  simp [perturbation, cutoff, Profiles.step_ge_one hs]

variable [InnerProductSpace ℝ E]

theorem drive_contDiff {w : ℝ} (hw : 0 < w) (c : E) (n : WithTop ℕ∞) :
    ContDiff ℝ n (drive w c) := by
  unfold drive
  apply contDiff_const.mul
  apply ContDiff.sqrt
  · exact contDiff_const.add ((contDiff_id.sub contDiff_const).norm_sq ℝ)
  · intro u
    nlinarith [sq_nonneg ‖u - c‖]

theorem publicPotential_contDiff {R : ℝ} (hR : 0 < R) (n : WithTop ℕ∞) :
    ContDiff ℝ n (publicPotential R : E → ℝ) := by
  unfold publicPotential
  apply contDiff_const.mul
  apply ContDiff.sub _ contDiff_const
  apply ContDiff.sqrt
  · exact contDiff_const.add (contDiff_id.norm_sq ℝ)
  · intro u
    positivity

/-- Actual global C3 regularity of every scalar in the localized block. -/
theorem localized_contDiff {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (c : E) :
    ContDiff ℝ 3 (potential R w c) ∧ ContDiff ℝ 3 (incoming R w c) ∧
    ContDiff ℝ 3 (port w c) := by
  have hs : ContDiff ℝ 3 (fun u : E => ‖u - c‖ ^ 2) :=
    (contDiff_id.sub contDiff_const).norm_sq ℝ
  have hc : ContDiff ℝ 3 (cutoff w c) :=
    contDiff_const.sub (Profiles.contDiff_step.comp ((hs.sub contDiff_const).div_const _))
  have hk : ContDiff ℝ 3 (well R w c) :=
    contDiff_const.add (contDiff_const.mul hs)
  have hv : ContDiff ℝ 3 (potential R w c) :=
    (publicPotential_contDiff hR 3).add (hc.mul (hk.sub (publicPotential_contDiff hR 3)))
  exact ⟨hv, (hv.sub (drive_contDiff hw c 3)).add contDiff_const,
    contDiff_const.sub (Profiles.contDiff_step.comp ((hs.sub contDiff_const).div_const _))⟩

section Gradient

variable [CompleteSpace E]

/-- The actual Hilbert-space gradient of the manuscript's drive potential. -/
theorem drive_hasGradientAt {w : ℝ} (hw : 0 < w) (c u : E) :
    HasGradientAt (drive w c)
      ((16 / Real.sqrt (w ^ 2 + ‖u - c‖ ^ 2)) • (u - c)) u := by
  have hp : 0 < w ^ 2 + ‖u - c‖ ^ 2 := by positivity
  have hsq := ((hasFDerivAt_id u).sub_const c).norm_sq
  have h := (((hasFDerivAt_const (w ^ 2) u).add hsq).sqrt (ne_of_gt hp)).const_mul 16
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  ext z
  simp [InnerProductSpace.toDual_apply, real_inner_smul_left]
  ring

theorem cancelled_hasGradientAt {w : ℝ} (hw : 0 < w) (R : ℝ) (c u : E) :
    HasGradientAt (fun x => potential R w c x - incoming R w c x)
      ((16 / Real.sqrt (w ^ 2 + ‖u - c‖ ^ 2)) • (u - c)) u := by
  have h := (drive_hasGradientAt hw c u).hasFDerivAt.sub_const (512 * R)
  rw [hasGradientAt_iff_hasFDerivAt]
  simpa only [cancellation] using h

theorem cancelled_gradient {w : ℝ} (hw : 0 < w) (R : ℝ) (c u : E) :
    gradient (fun x => potential R w c x - incoming R w c x) u =
      (16 / Real.sqrt (w ^ 2 + ‖u - c‖ ^ 2)) • (u - c) :=
  (cancelled_hasGradientAt hw R c u).gradient

theorem cancelled_gradient_norm {w : ℝ} (hw : 0 < w) (R : ℝ) (c u : E) :
    ‖gradient (fun x => potential R w c x - incoming R w c x) u‖ =
      16 * ‖u - c‖ / Real.sqrt (w ^ 2 + ‖u - c‖ ^ 2) := by
  rw [cancelled_gradient hw, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  ring

theorem well_hasGradientAt (R w : ℝ) (c u : E) :
    HasGradientAt (well R w c) ((16 / w) • (u - c)) u := by
  have h := (((hasFDerivAt_id u).sub_const c).norm_sq.const_mul (8 / w)).const_add
    (publicPotential R c - 160 * w)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  ext z
  simp [InnerProductSpace.toDual_apply, real_inner_smul_left]
  ring

theorem potential_hasGradientAt_of_norm_lt_two_mul {w : ℝ} (hw : 0 < w)
    (R : ℝ) (c u : E) (hu : ‖u - c‖ < 2 * w) :
    HasGradientAt (potential R w c) ((16 / w) • (u - c)) u := by
  apply (well_hasGradientAt R w c u).congr_of_eventuallyEq
  have hc : ContinuousAt (fun x : E => ‖x - c‖) u :=
    (continuous_id.sub continuous_const).norm.continuousAt
  have hev : ∀ᶠ x in 𝓝 u, ‖x - c‖ < 2 * w := hc.preimage_mem_nhds (gt_mem_nhds hu)
  filter_upwards [hev] with x hx
  exact potential_eq_well_of_norm_le_two_mul hw hx.le

def portSlope (w : ℝ) (c u : E) : ℝ :=
  2 * Profiles.step₁ ((‖u - c‖ ^ 2 - w ^ 2) / (3 * w ^ 2)) / (3 * w ^ 2)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem portSlope_nonneg {w : ℝ} (hw : 0 < w) (c u : E) : 0 ≤ portSlope w c u := by
  have h := (Profiles.derivative_bounds ((‖u - c‖ ^ 2 - w ^ 2) / (3 * w ^ 2))).1
  rw [Profiles.deriv_step] at h
  unfold portSlope
  positivity

theorem port_hasGradientAt (w : ℝ) (c u : E) :
    HasGradientAt (port w c) ((-portSlope w c u) • (u - c)) u := by
  have hs := ((((hasFDerivAt_id u).sub_const c).norm_sq).sub_const (w ^ 2)).mul_const
    ((3 * w ^ 2)⁻¹)
  simp only [← div_eq_mul_inv] at hs
  have h := ((Profiles.step_derivative _).comp_hasFDerivAt u hs).const_sub 1
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  ext z
  simp [InnerProductSpace.toDual_apply, real_inner_smul_left, portSlope]
  ring

theorem incoming_hasGradientAt_of_norm_lt_two_mul {w : ℝ} (hw : 0 < w)
    (R : ℝ) (c u : E) (hu : ‖u - c‖ < 2 * w) :
    HasGradientAt (incoming R w c)
      ((16 / w) • (u - c) - (16 / Real.sqrt (w ^ 2 + ‖u - c‖ ^ 2)) • (u - c)) u := by
  have h := ((potential_hasGradientAt_of_norm_lt_two_mul hw R c u hu).hasFDerivAt.sub
    (drive_hasGradientAt hw c u).hasFDerivAt).add_const (512 * R)
  rw [hasGradientAt_iff_hasFDerivAt]
  simpa only [incoming, map_sub] using h

omit [CompleteSpace E] in
/-- The collinear-vector estimate underlying one-sided robustness. -/
theorem radial_robustness {w τ ζ β : ℝ} {z : E}
    (hw : 0 < w) (ht : w ≤ ‖z‖) (hτ : τ ≤ 1) (hζ : ζ ≤ 0) (hβ : 0 ≤ β) :
    16 / Real.sqrt 2 ≤
      ‖(16 / w) • z - τ • ((16 / w) • z -
        (16 / Real.sqrt (w ^ 2 + ‖z‖ ^ 2)) • z) + ζ • ((-β) • z)‖ := by
  have hp : 0 < w ^ 2 + ‖z‖ ^ 2 := by positivity
  have hs := Real.sq_sqrt hp.le
  have hroot : 0 < Real.sqrt (w ^ 2 + ‖z‖ ^ 2) := Real.sqrt_pos.2 hp
  have htwo : 0 < Real.sqrt 2 := by positivity
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hwroot : w ≤ Real.sqrt (w ^ 2 + ‖z‖ ^ 2) := by
    apply (sq_le_sq₀ hw.le hroot.le).1
    rw [hs]
    nlinarith [sq_nonneg ‖z‖]
  have hAB : 16 / Real.sqrt (w ^ 2 + ‖z‖ ^ 2) ≤ 16 / w := by
    apply (div_le_div_iff₀ hroot hw).2
    nlinarith
  have hrad : Real.sqrt (w ^ 2 + ‖z‖ ^ 2) ≤ Real.sqrt 2 * ‖z‖ := by
    apply (sq_le_sq₀ hroot.le (by positivity)).1
    rw [hs, mul_pow, hs2]
    nlinarith [norm_nonneg z]
  have hB : 16 / Real.sqrt 2 ≤ (16 / Real.sqrt (w ^ 2 + ‖z‖ ^ 2)) * ‖z‖ := by
    rw [div_mul_eq_mul_div]
    apply (div_le_div_iff₀ htwo hroot).2
    nlinarith
  let C : ℝ := 16 / w - τ * (16 / w - 16 / Real.sqrt (w ^ 2 + ‖z‖ ^ 2)) - ζ * β
  have hC : 16 / Real.sqrt (w ^ 2 + ‖z‖ ^ 2) ≤ C := by
    have hprod := mul_nonneg (by linarith : 0 ≤ 1 - τ) (sub_nonneg.2 hAB)
    have hz := mul_nonpos_of_nonpos_of_nonneg hζ hβ
    dsimp [C]
    nlinarith
  have hC0 : 0 ≤ C := le_trans (by positivity) hC
  have heq : (16 / w) • z - τ • ((16 / w) • z -
        (16 / Real.sqrt (w ^ 2 + ‖z‖ ^ 2)) • z) + ζ • ((-β) • z) = C • z := by
    dsimp [C]
    module
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hC0]
  exact hB.trans (mul_le_mul_of_nonneg_right hC (norm_nonneg z))

/-- Equation (loc-robust) for the actual gradients of the literal localized block.
The scalar upper bound on `τ` alone suffices for this slightly stronger form. -/
theorem localized_robustness {w τ ζ : ℝ} (hw : 0 < w) (R : ℝ) (c u : E)
    (hlo : w < ‖u - c‖) (hhi : ‖u - c‖ < 2 * w) (hτ : τ ≤ 1) (hζ : ζ ≤ 0) :
    16 / Real.sqrt 2 ≤
      ‖gradient (potential R w c) u - τ • gradient (incoming R w c) u +
        ζ • gradient (port w c) u‖ := by
  rw [(potential_hasGradientAt_of_norm_lt_two_mul hw R c u hhi).gradient,
    (incoming_hasGradientAt_of_norm_lt_two_mul hw R c u hhi).gradient,
    (port_hasGradientAt w c u).gradient]
  exact radial_robustness hw hlo.le hτ hζ (portSlope_nonneg hw c u)

theorem one_lt_sixteen_div_sqrt_two : (1 : ℝ) < 16 / Real.sqrt 2 := by
  have htwo : 0 < Real.sqrt 2 := by positivity
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  apply (lt_div_iff₀ htwo).2
  nlinarith

theorem localized_transition_excludes_small_gradient {w τ ζ : ℝ} (hw : 0 < w)
    (R : ℝ) (c u : E) (hlo : w < ‖u - c‖) (hhi : ‖u - c‖ < 2 * w)
    (hτ : τ ≤ 1) (hζ : ζ ≤ 0) :
    1 < ‖gradient (potential R w c) u - τ • gradient (incoming R w c) u +
      ζ • gradient (port w c) u‖ :=
  one_lt_sixteen_div_sqrt_two.trans_le (localized_robustness hw R c u hlo hhi hτ hζ)

/-- The first assertion of localized activation, with the manuscript's constant 255. -/
theorem small_gradient_distance {w : ℝ} (hw : 0 < w) (R : ℝ) (c u : E)
    (hg : ‖gradient (fun x => potential R w c x - incoming R w c x) u‖ ≤ 1) :
    ‖u - c‖ ≤ w / Real.sqrt 255 := by
  rw [cancelled_gradient_norm hw] at hg
  have hp : 0 < w ^ 2 + ‖u - c‖ ^ 2 := by positivity
  have hs := Real.sq_sqrt (le_of_lt hp)
  have hroot : 0 < Real.sqrt (w ^ 2 + ‖u - c‖ ^ 2) := Real.sqrt_pos.2 hp
  have hmul : 16 * ‖u - c‖ ≤ Real.sqrt (w ^ 2 + ‖u - c‖ ^ 2) := by
    exact (div_le_one hroot).1 hg
  have hbound : 255 * ‖u - c‖ ^ 2 ≤ w ^ 2 := by
    have hsqle := mul_self_le_mul_self (by positivity : 0 ≤ 16 * ‖u - c‖) hmul
    nlinarith
  have h255 : 0 < Real.sqrt 255 := by positivity
  have hs255 : (Real.sqrt 255) ^ 2 = 255 := Real.sq_sqrt (by norm_num)
  rw [le_div_iff₀ h255]
  have hprod : 0 ≤ ‖u - c‖ * Real.sqrt 255 := by positivity
  nlinarith [sq_nonneg (‖u - c‖ * Real.sqrt 255 + w)]

/-- A gradient of norm at most one opens the literal completion port. -/
theorem small_gradient_opens_port {w : ℝ} (hw : 0 < w) (R : ℝ) (c u : E)
    (hg : ‖gradient (fun x => potential R w c x - incoming R w c x) u‖ ≤ 1) :
    ‖u - c‖ < w ∧ port w c u = 1 := by
  have hd := small_gradient_distance hw R c u hg
  have hs255 : (Real.sqrt 255) ^ 2 = 255 := Real.sq_sqrt (by norm_num)
  have hroot : 1 < Real.sqrt 255 := by nlinarith [Real.sqrt_nonneg 255]
  have hdiv : w / Real.sqrt 255 < w := (div_lt_self hw hroot)
  have hdist : ‖u - c‖ < w := lt_of_le_of_lt hd hdiv
  exact ⟨hdist, port_eq_one_of_norm_le hw hdist.le⟩

end Gradient

omit [InnerProductSpace ℝ E] in
/-- The geometric separation in the adjacent-level identification appendix.
This is independent of the minimizer-existence claim used there. -/
theorem adjacent_level_separation {R w : ℝ} {a b u : E}
    (hw : 0 < w) (hscale : 16 * w ≤ R)
    (ha : ‖a‖ = R) (hb : ‖b‖ = 6 * R) (hu : ‖u - a‖ < w) :
    9 * w < ‖u - b‖ := by
  have h1 : ‖b - a‖ ≤ ‖b - u‖ + ‖u - a‖ := by
    simpa only [dist_eq_norm] using dist_triangle b u a
  have h2 := norm_sub_norm_le b a
  rw [hb, ha] at h2
  rw [norm_sub_rev b u] at h1
  nlinarith

omit [InnerProductSpace ℝ E] in
theorem adjacent_parent_port_zero {R w : ℝ} {a b u : E}
    (hw : 0 < w) (hscale : 16 * w ≤ R)
    (ha : ‖a‖ = R) (hb : ‖b‖ = 6 * R) (hu : ‖u - a‖ < w) :
    port (3 * w) b u = 0 ∧ perturbation (6 * R) (3 * w) b u = 0 := by
  have hdist := adjacent_level_separation hw hscale ha hb hu
  constructor
  · exact port_eq_zero_of_two_mul_le_norm (by positivity) (by linarith)
  · exact perturbation_eq_zero_of_three_mul_le_norm (by positivity) (by linarith)

end GradientHessian.Localized
