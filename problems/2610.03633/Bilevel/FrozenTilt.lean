import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Frozen linear tilt: deterministic core of Appendix B of `0113.tex`

This module proves vector Taylor remainders from Lipschitz Fréchet derivatives,
displacement and stability from strong monotonicity, an inverse norm bound from
coercivity, and the ideal frozen-tilt bias estimate. It does not assert that all
the paper's primitive assumptions have already been connected to these analytic
hypotheses, or that the stochastic implementation/query theorem is established.
-/

namespace Bilevel.FrozenTilt

noncomputable section

open scoped RealInnerProductSpace

section Taylor

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Taylor's exact one-half remainder bound on a unit parameter interval. -/
theorem path_remainder_bound (f f' : ℝ → F) (M : ℝ)
    (hf : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' s) s)
    (hvariation : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖f' s - f' 0‖ ≤ M * s) :
    ‖f 1 - f 0 - f' 0‖ ≤ M / 2 := by
  let r : ℝ → F := fun s => f s - f 0 - s • f' 0
  have hr : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt r (f' s - f' 0) s := by
    intro s hs
    simpa [r] using ((hf s hs).sub_const (f 0)).sub ((hasDerivAt_id s).smul_const (f' 0))
  have hc : ContinuousOn r (Set.Icc (0 : ℝ) 1) :=
    fun s hs => (hr s hs).continuousAt.continuousWithinAt
  have hb : ∀ s : ℝ, HasDerivAt (fun u : ℝ => M / 2 * u ^ 2) (M * s) s := by
    intro s
    convert (hasDerivAt_pow 2 s).const_mul (M / 2) using 1
    ring
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary hc
    (fun s hs => (hr s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt)
    (show ‖r 0‖ ≤ M / 2 * (0 : ℝ) ^ 2 by simp [r]) hb
    (fun s hs => hvariation s ⟨hs.1, hs.2.le⟩)
    (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by constructor <;> norm_num)
  simpa [r] using h

/-- A Lipschitz Fréchet derivative gives the vector Taylor remainder used in the paper. -/
theorem taylor_remainder_bound (g : E → F) (D : E → E →L[ℝ] F)
    (y d : E) (ρ : ℝ)
    (hD : ∀ z, HasFDerivAt g (D z) z)
    (hvariation : ∀ z w, ‖D z - D w‖ ≤ ρ * ‖z - w‖) :
    ‖g (y + d) - g y - D y d‖ ≤ ρ / 2 * ‖d‖ ^ 2 := by
  have hpath : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun u : ℝ => g (y + u • d)) (D (y + s • d) d) s := by
    intro s _
    have hline : HasDerivAt (fun u : ℝ => y + u • d) d s := by
      simpa using ((hasDerivAt_id s).smul_const d).const_add y
    exact (hD _).comp_hasDerivAt s hline
  have hv : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖D (y + s • d) d - D (y + (0 : ℝ) • d) d‖ ≤ (ρ * ‖d‖ ^ 2) * s := by
    intro s hs
    simp only [zero_smul, add_zero]
    calc
      ‖D (y + s • d) d - D y d‖ = ‖(D (y + s • d) - D y) d‖ := rfl
      _ ≤ ‖D (y + s • d) - D y‖ * ‖d‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (ρ * ‖y + s • d - y‖) * ‖d‖ :=
        mul_le_mul_of_nonneg_right (hvariation _ _) (norm_nonneg d)
      _ = (ρ * ‖d‖ ^ 2) * s := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
        ring
  have h := path_remainder_bound _ _ (ρ * ‖d‖ ^ 2) hpath hv
  simpa [mul_div_assoc, div_mul_eq_mul_div] using h

end Taylor

section Inverse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Coercivity bounds the inverse operator norm by the reciprocal modulus. -/
theorem inverse_norm_bound (H J : E →L[ℝ] E) {μ : ℝ} (hμ : 0 < μ)
    (hcoercive : ∀ v, μ * ‖v‖ ^ 2 ≤ ⟪H v, v⟫)
    (hright : ∀ v, H (J v) = v) : ‖J‖ ≤ μ⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hμ.le)
  intro v
  have h := (hcoercive (J v)).trans (real_inner_le_norm (H (J v)) (J v))
  rw [hright] at h
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ hμ).mpr
  by_cases hz : ‖J v‖ = 0
  · simpa only [hz, zero_mul] using norm_nonneg v
  · have hp : 0 < ‖J v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

end Inverse

section Monotonicity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The precise monotonicity property used for the lower gradient. -/
def StrongMonotone (g : E → E) (μ : ℝ) : Prop :=
  ∀ u v, μ * ‖u - v‖ ^ 2 ≤ ⟪g u - g v, u - v⟫

/-- Two tilted stationary points are Lipschitz in the frozen direction. -/
theorem solution_stability {g : E → E} {μ t : ℝ} {u v a b : E}
    (hμ : 0 < μ) (ht : 0 < t) (hg : StrongMonotone g μ)
    (hu : g u = -t • a) (hv : g v = -t • b) :
    ‖u - v‖ ≤ t / μ * ‖a - b‖ := by
  have h := (hg u v).trans (real_inner_le_norm (g u - g v) (u - v))
  have hd : g u - g v = -t • (a - b) := by rw [hu, hv, smul_sub]
  rw [hd, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos ht] at h
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hμ).mpr
  by_cases hz : ‖u - v‖ = 0
  · simp only [hz, zero_mul]
    exact mul_nonneg ht.le (norm_nonneg _)
  · have hp : 0 < ‖u - v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hc : ‖u - v‖ * μ ≤ t * ‖a - b‖ := by nlinarith
    exact hc

/-- The unperturbed/tilted displacement estimate, with a norm bound on the tilt. -/
theorem solution_displacement {g : E → E} {μ t C : ℝ} {y₀ yₜ a : E}
    (hμ : 0 < μ) (ht : 0 < t) (hg : StrongMonotone g μ)
    (hzero : g y₀ = 0) (htilt : g yₜ = -t • a) (ha : ‖a‖ ≤ C) :
    ‖yₜ - y₀‖ ≤ t * C / μ := by
  have h := solution_stability hμ ht hg htilt (show g y₀ = -t • (0 : E) by simp [hzero])
  simp only [sub_zero] at h
  calc
    ‖yₜ - y₀‖ ≤ t / μ * ‖a‖ := h
    _ ≤ t / μ * C := mul_le_mul_of_nonneg_left ha (div_nonneg ht.le hμ.le)
    _ = t * C / μ := by ring

end Monotonicity

section Bias

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The ideal finite-difference estimator, with the upper gradient frozen. -/
def estimator (fₓ : F) (gₓ : E → F) (y₀ yₜ : E) (t : ℝ) : F :=
  fₓ + t⁻¹ • (gₓ yₜ - gₓ y₀)

/-- Hypergradient expression at the unperturbed lower solution. -/
def hypergradient (fₓ : F) (B : E →L[ℝ] F) (J : E →L[ℝ] E) (a : E) : F :=
  fₓ - B (J a)

/-- Exact error identity from the lower and mixed Taylor expansions. -/
theorem residual_identity (H J : E →L[ℝ] E) (B : E →L[ℝ] F)
    (hleft : ∀ v, J (H v) = v) {t : ℝ} (ht : t ≠ 0)
    (d a eᵧ : E) (eₓ fₓ : F) (hstationary : H d + eᵧ = -t • a) :
    fₓ + t⁻¹ • (B d + eₓ) - hypergradient fₓ B J a =
      t⁻¹ • (eₓ - B (J eᵧ)) := by
  have h := congrArg J hstationary
  simp only [map_add, map_smul, hleft] at h
  have hd : d = -t • J a - J eᵧ := eq_sub_of_add_eq h
  rw [hd]
  simp only [map_sub, map_smul, hypergradient]
  simp only [smul_add, smul_sub, smul_neg, smul_smul, mul_neg, inv_mul_cancel₀ ht,
    neg_smul, one_smul]
  abel

/-- Residual norm estimate before substituting the displacement bound. -/
theorem residual_bound (J : E →L[ℝ] E) (B : E →L[ℝ] F)
    {t μ L ρ : ℝ} (ht : 0 < t) (hμ : 0 < μ)
    (hL : 0 ≤ L)
    (hJ : ‖J‖ ≤ μ⁻¹) (hB : ‖B‖ ≤ L)
    (d eᵧ : E) (eₓ : F)
    (hey : ‖eᵧ‖ ≤ ρ / 2 * ‖d‖ ^ 2) (hex : ‖eₓ‖ ≤ ρ / 2 * ‖d‖ ^ 2) :
    ‖t⁻¹ • (eₓ - B (J eᵧ))‖ ≤
      t⁻¹ * ((1 + L / μ) * (ρ / 2 * ‖d‖ ^ 2)) := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ht.le)
  calc
    ‖eₓ - B (J eᵧ)‖ ≤ ‖eₓ‖ + ‖B (J eᵧ)‖ := norm_sub_le _ _
    _ ≤ ‖eₓ‖ + ‖B‖ * (‖J‖ * ‖eᵧ‖) := by
      exact add_le_add_left ((B.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (J.le_opNorm _) (norm_nonneg B))) _
    _ ≤ ρ / 2 * ‖d‖ ^ 2 + L * (μ⁻¹ * (ρ / 2 * ‖d‖ ^ 2)) := by gcongr
    _ = (1 + L / μ) * (ρ / 2 * ‖d‖ ^ 2) := by ring

/-- The exact bias coefficient in equation (B.3), conditional on explicit Taylor data. -/
theorem bias_bound (H J : E →L[ℝ] E) (B : E →L[ℝ] F)
    (hleft : ∀ v, J (H v) = v) {t μ L ρ C : ℝ}
    (ht : 0 < t) (hμ : 0 < μ) (hL : 0 ≤ L) (hρ : 0 ≤ ρ)
    (hJ : ‖J‖ ≤ μ⁻¹) (hB : ‖B‖ ≤ L)
    (gₓ : E → F) (y₀ yₜ a eᵧ : E) (eₓ fₓ : F)
    (hstationary : H (yₜ - y₀) + eᵧ = -t • a)
    (hmixed : gₓ yₜ - gₓ y₀ = B (yₜ - y₀) + eₓ)
    (hdisplacement : ‖yₜ - y₀‖ ≤ t * C / μ)
    (hey : ‖eᵧ‖ ≤ ρ / 2 * ‖yₜ - y₀‖ ^ 2)
    (hex : ‖eₓ‖ ≤ ρ / 2 * ‖yₜ - y₀‖ ^ 2) :
    ‖estimator fₓ gₓ y₀ yₜ t - hypergradient fₓ B J a‖ ≤
      ((1 + L / μ) * ρ * C ^ 2 / (2 * μ ^ 2)) * t := by
  rw [estimator, hmixed, residual_identity H J B hleft ht.ne' _ _ _ _ _ hstationary]
  calc
    ‖t⁻¹ • (eₓ - B (J eᵧ))‖ ≤
      t⁻¹ * ((1 + L / μ) * (ρ / 2 * ‖yₜ - y₀‖ ^ 2)) :=
        residual_bound J B ht hμ hL hJ hB _ _ _ hey hex
    _ ≤ t⁻¹ * ((1 + L / μ) * (ρ / 2 * (t * C / μ) ^ 2)) := by
      gcongr
    _ = ((1 + L / μ) * ρ * C ^ 2 / (2 * μ ^ 2)) * t := by
      field_simp
      ring

/-- Zero Hessian variation makes both explicit remainder terms vanish. -/
theorem zero_variation_exact (H J : E →L[ℝ] E) (B : E →L[ℝ] F)
    (hleft : ∀ v, J (H v) = v) {t : ℝ} (ht : t ≠ 0)
    (gₓ : E → F) (y₀ yₜ a : E) (fₓ : F)
    (hstationary : H (yₜ - y₀) = -t • a)
    (hmixed : gₓ yₜ - gₓ y₀ = B (yₜ - y₀)) :
    estimator fₓ gₓ y₀ yₜ t = hypergradient fₓ B J a := by
  apply sub_eq_zero.mp
  have h := residual_identity H J B hleft ht (yₜ - y₀) a 0 0 fₓ
    (by simpa using hstationary)
  simpa [estimator, hmixed] using h

end Bias

section EstimatorStability

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Analytic frozen-tilt bias theorem. Both Taylor estimates are derived here.

The hypotheses expose the lower gradient's strong monotonicity and the inverse
Hessian bound rather than silently assuming a primitive-to-analytic bridge.
-/
theorem ideal_estimator_bias (gᵧ : E → E) (gₓ : E → F)
    (Dᵧ : E → E →L[ℝ] E) (Dₓ : E → E →L[ℝ] F) (J : E →L[ℝ] E)
    (y₀ yₜ a : E) (fₓ : F) {t μ L ρ C : ℝ}
    (ht : 0 < t) (hμ : 0 < μ) (hL : 0 ≤ L) (hρ : 0 ≤ ρ)
    (hstrong : StrongMonotone gᵧ μ)
    (hzero : gᵧ y₀ = 0) (htilt : gᵧ yₜ = -t • a) (ha : ‖a‖ ≤ C)
    (hDy : ∀ z, HasFDerivAt gᵧ (Dᵧ z) z)
    (hDx : ∀ z, HasFDerivAt gₓ (Dₓ z) z)
    (hvy : ∀ z w, ‖Dᵧ z - Dᵧ w‖ ≤ ρ * ‖z - w‖)
    (hvx : ∀ z w, ‖Dₓ z - Dₓ w‖ ≤ ρ * ‖z - w‖)
    (hleft : ∀ v, J (Dᵧ y₀ v) = v)
    (hJ : ‖J‖ ≤ μ⁻¹) (hB : ‖Dₓ y₀‖ ≤ L) :
    ‖estimator fₓ gₓ y₀ yₜ t - hypergradient fₓ (Dₓ y₀) J a‖ ≤
      ((1 + L / μ) * ρ * C ^ 2 / (2 * μ ^ 2)) * t := by
  let ey := gᵧ yₜ - gᵧ y₀ - Dᵧ y₀ (yₜ - y₀)
  let ex := gₓ yₜ - gₓ y₀ - Dₓ y₀ (yₜ - y₀)
  have hstat : Dᵧ y₀ (yₜ - y₀) + ey = -t • a := by
    dsimp [ey]
    rw [hzero, htilt]
    abel
  have hmix : gₓ yₜ - gₓ y₀ = Dₓ y₀ (yₜ - y₀) + ex := by dsimp [ex]; abel
  have hey : ‖ey‖ ≤ ρ / 2 * ‖yₜ - y₀‖ ^ 2 := by
    simpa [ey] using taylor_remainder_bound gᵧ Dᵧ y₀ (yₜ - y₀) ρ hDy hvy
  have hex : ‖ex‖ ≤ ρ / 2 * ‖yₜ - y₀‖ ^ 2 := by
    simpa [ex] using taylor_remainder_bound gₓ Dₓ y₀ (yₜ - y₀) ρ hDx hvx
  exact bias_bound (Dᵧ y₀) J (Dₓ y₀) hleft ht hμ hL hρ hJ hB
    gₓ y₀ yₜ a ey ex fₓ hstat hmix
    (solution_displacement hμ ht hstrong hzero htilt ha) hey hex

/-- Direction stability of the ideal estimator, equation (B.4). -/
theorem estimator_stability {gᵧ : E → E} {gₓ : E → F} {μ t L : ℝ}
    {u v y₀ a b : E} (fₓ : F)
    (hμ : 0 < μ) (ht : 0 < t) (hL : 0 ≤ L)
    (hg : StrongMonotone gᵧ μ)
    (hu : gᵧ u = -t • a) (hv : gᵧ v = -t • b)
    (hx : ∀ z w, ‖gₓ z - gₓ w‖ ≤ L * ‖z - w‖) :
    ‖estimator fₓ gₓ y₀ u t - estimator fₓ gₓ y₀ v t‖ ≤ L / μ * ‖a - b‖ := by
  have he : estimator fₓ gₓ y₀ u t - estimator fₓ gₓ y₀ v t =
      t⁻¹ • (gₓ u - gₓ v) := by unfold estimator; module
  rw [he, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht]
  calc
    t⁻¹ * ‖gₓ u - gₓ v‖ ≤ t⁻¹ * (L * ‖u - v‖) := by gcongr; exact hx u v
    _ ≤ t⁻¹ * (L * (t / μ * ‖a - b‖)) := by
      gcongr
      exact solution_stability hμ ht hg hu hv
    _ = L / μ * ‖a - b‖ := by field_simp; ring

end EstimatorStability

end

end Bilevel.FrozenTilt
