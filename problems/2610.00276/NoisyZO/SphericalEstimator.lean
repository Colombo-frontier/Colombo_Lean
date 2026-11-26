import NoisyZO.BetaFourBall
import NoisyZO.SphereBallDivergence
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The explicit spherical estimator at `β = 4`

This file defines the manuscript's central spherical differences and their
two-scale combination.  It proves the exact signal/noise decomposition, the
dimension-linear pathwise signal bound, and measure-level mean and
second-moment consequences.  For the concrete uniform-sphere law, the
surface-to-ball smoothing identity is supplied by `SphereBallDivergence`;
the generic arbitrary-measure mean theorem also remains available.
-/

open MeasureTheory Metric Set
open scoped Gradient InnerProductSpace

namespace NoisyZO

noncomputable section

/-- The noise-free spherical central-difference vector at radius `r`. -/
def centralDifferenceSignal (d : ℕ) (f : Point d → ℝ)
    (x : Point d) (r : ℝ) (u : Point d) : Point d :=
  (((d : ℝ) / (2 * r)) * (f (x + r • u) - f (x - r • u))) • u

/-- The contribution of two scalar oracle noises to a spherical central
difference. -/
def centralDifferenceNoise (d : ℕ) (r : ℝ) (u : Point d)
    (ξplus ξminus : ℝ) : Point d :=
  (((d : ℝ) / (2 * r)) * (ξplus - ξminus)) • u

/-- The explicit two-radius noise-free estimator for `β = 4`. -/
def betaFourSphericalSignal (d : ℕ) (f : Point d → ℝ)
    (x : Point d) (h : ℝ) (u : Point d) : Point d :=
  (-1 / 3 : ℝ) • centralDifferenceSignal d f x h u +
    (4 / 3 : ℝ) • centralDifferenceSignal d f x (h / 2) u

/-- The exact surface-to-ball identity for one central-difference radius. -/
theorem integral_centralDifferenceSignal_eq_ballSmoothedField
    {d : ℕ} (hd : 0 < d) (f : Point d → ℝ) (hf : ContDiff ℝ 1 f)
    (x : Point d) {r : ℝ} (hr : 0 < r) :
    (∫ u, centralDifferenceSignal d f x r u
        ∂(uniformUnitSphere d hd : Measure (Point d))) =
      ballSmoothedField d (∇ f) x r := by
  let gp : Point d → ℝ := fun y ↦ f (x + r • y)
  let gm : Point d → ℝ := fun y ↦ f (x + (-r) • y)
  have hgp : ContDiff ℝ 1 gp := by
    apply hf.comp
    fun_prop
  have hgm : ContDiff ℝ 1 gm := by
    apply hf.comp
    fun_prop
  have hp := integral_uniformUnitSphere_dim_smul_eq_uniformUnitBall_gradient
    hd gp hgp
  have hm := integral_uniformUnitSphere_dim_smul_eq_uniformUnitBall_gradient
    hd gm hgm
  have hgradp : (fun y ↦ ∇ gp y) =
      fun y ↦ r • ∇ f (x + r • y) := by
    funext y
    exact gradient_affine_smul f hf x r y
  have hgradm : (fun y ↦ ∇ gm y) =
      fun y ↦ (-r) • ∇ f (x + (-r) • y) := by
    funext y
    exact gradient_affine_smul f hf x (-r) y
  rw [hgradp, integral_smul] at hp
  rw [integral_smul] at hp
  rw [hgradm, integral_smul] at hm
  rw [integral_smul] at hm
  have hsym :
      (∫ y, ∇ f (x + (-r) • y)
          ∂(uniformUnitBall d : Measure (Point d))) =
        ∫ y, ∇ f (x + r • y)
          ∂(uniformUnitBall d : Measure (Point d)) := by
    have hpres : MeasurePreserving (fun y : Point d ↦ -y)
        (uniformUnitBall d : Measure (Point d))
        (uniformUnitBall d : Measure (Point d)) :=
      ⟨measurable_neg, uniformUnitBall_isCentrallySymmetric d⟩
    have h := hpres.integral_comp measurableEmbedding_neg
      (fun y : Point d ↦ ∇ f (x + r • y))
    simpa [neg_smul] using h
  have hip : Integrable
      (fun u : Point d ↦ (d : ℝ) • (gp u • u))
      (uniformUnitSphere d hd : Measure (Point d)) :=
    continuous_integrable_uniformUnitSphere hd _ (by
      dsimp only [gp]
      fun_prop)
  have him : Integrable
      (fun u : Point d ↦ (d : ℝ) • (gm u • u))
      (uniformUnitSphere d hd : Measure (Point d)) :=
    continuous_integrable_uniformUnitSphere hd _ (by
      dsimp only [gm]
      fun_prop)
  rw [show (fun u ↦ centralDifferenceSignal d f x r u) =
      fun u ↦ (1 / (2 * r) : ℝ) •
        ((d : ℝ) • (gp u • u) - (d : ℝ) • (gm u • u)) by
    funext u
    unfold centralDifferenceSignal
    dsimp only [gp, gm]
    simp only [neg_smul, sub_eq_add_neg]
    field_simp [hr.ne']
    module]
  rw [integral_smul, integral_sub hip him, integral_smul, integral_smul,
    hp, hm, hsym]
  unfold ballSmoothedField
  have hc : (1 / (2 * r) : ℝ) * (r - (-r)) = 1 := by
    field_simp [hr.ne']
    norm_num
  rw [← sub_smul, smul_smul, hc, one_smul]

/-- The manuscript's two-radius `β = 4` signal has exactly the corresponding
two-radius uniform-ball mean. -/
theorem integral_betaFourSphericalSignal_eq_betaFourBallField
    {d : ℕ} (hd : 0 < d) (f : Point d → ℝ) (hf : ContDiff ℝ 1 f)
    (x : Point d) {h : ℝ} (hh : 0 < h) :
    (∫ u, betaFourSphericalSignal d f x h u
        ∂(uniformUnitSphere d hd : Measure (Point d))) =
      betaFourBallField d (∇ f) x h := by
  have hout : Integrable (centralDifferenceSignal d f x h)
      (uniformUnitSphere d hd : Measure (Point d)) :=
    continuous_integrable_uniformUnitSphere hd _ (by
      unfold centralDifferenceSignal
      fun_prop)
  have hin : Integrable (centralDifferenceSignal d f x (h / 2))
      (uniformUnitSphere d hd : Measure (Point d)) :=
    continuous_integrable_uniformUnitSphere hd _ (by
      unfold centralDifferenceSignal
      fun_prop)
  unfold betaFourSphericalSignal betaFourBallField
  change (∫ u,
      ((-1 / 3 : ℝ) • centralDifferenceSignal d f x h) u +
        ((4 / 3 : ℝ) • centralDifferenceSignal d f x (h / 2)) u
        ∂(uniformUnitSphere d hd : Measure (Point d))) = _
  rw [integral_add (Integrable.smul (-1 / 3 : ℝ) hout)
      (Integrable.smul (4 / 3 : ℝ) hin)]
  simp only [Pi.smul_apply]
  rw [integral_smul, integral_smul,
    integral_centralDifferenceSignal_eq_ballSmoothedField hd f hf x hh,
    integral_centralDifferenceSignal_eq_ballSmoothedField hd f hf x (by positivity)]

/-- The corresponding linear combination of four fresh scalar noises. -/
def betaFourSphericalNoise (d : ℕ) (h : ℝ) (u : Point d)
    (ξOuterPlus ξOuterMinus ξInnerPlus ξInnerMinus : ℝ) : Point d :=
  (-1 / 3 : ℝ) •
      centralDifferenceNoise d h u ξOuterPlus ξOuterMinus +
    (4 / 3 : ℝ) •
      centralDifferenceNoise d (h / 2) u ξInnerPlus ξInnerMinus

/-- The scalar combination of the four independent noises. -/
def betaFourNoiseScalar
    (ξOuterPlus ξOuterMinus ξInnerPlus ξInnerMinus : ℝ) : ℝ :=
  8 * (ξInnerPlus - ξInnerMinus) - (ξOuterPlus - ξOuterMinus)

/-- The full four-query estimator, written as its signal plus noise parts. -/
def betaFourSphericalEstimator (d : ℕ) (f : Point d → ℝ)
    (x : Point d) (h : ℝ) (u : Point d)
    (ξOuterPlus ξOuterMinus ξInnerPlus ξInnerMinus : ℝ) : Point d :=
  betaFourSphericalSignal d f x h u +
    betaFourSphericalNoise d h u
      ξOuterPlus ξOuterMinus ξInnerPlus ξInnerMinus

/-- Algebraic form of the noise coefficient in equation (5.10). -/
theorem betaFourSphericalNoise_eq
    (d : ℕ) {h : ℝ} (hh : h ≠ 0) (u : Point d)
    (ξOuterPlus ξOuterMinus ξInnerPlus ξInnerMinus : ℝ) :
    betaFourSphericalNoise d h u
        ξOuterPlus ξOuterMinus ξInnerPlus ξInnerMinus =
      (((d : ℝ) / (6 * h)) *
        betaFourNoiseScalar
          ξOuterPlus ξOuterMinus ξInnerPlus ξInnerMinus) • u := by
  unfold betaFourSphericalNoise centralDifferenceNoise
  unfold betaFourNoiseScalar
  field_simp [hh]
  module

/-- On a unit direction, the squared norm of the estimator noise is the
squared scalar coefficient times the squared four-noise combination. -/
theorem norm_betaFourSphericalNoise_sq
    (d : ℕ) {h : ℝ} (hh : h ≠ 0) (u : Point d) (hu : ‖u‖ = 1)
    (ξOuterPlus ξOuterMinus ξInnerPlus ξInnerMinus : ℝ) :
    ‖betaFourSphericalNoise d h u
        ξOuterPlus ξOuterMinus ξInnerPlus ξInnerMinus‖ ^ 2 =
      ((d : ℝ) / (6 * h)) ^ 2 *
        (betaFourNoiseScalar
          ξOuterPlus ξOuterMinus ξInnerPlus ξInnerMinus) ^ 2 := by
  rw [betaFourSphericalNoise_eq d hh u,
    norm_smul, Real.norm_eq_abs, hu, mul_one, sq_abs]
  ring

/-- A scalar central-difference bound gives the standard `9d` pathwise
bound for one spherical scale. -/
theorem norm_centralDifferenceSignal_le
    (d : ℕ) (f : Point d → ℝ) (x : Point d) {r : ℝ} (hr : 0 < r)
    (u : Point d) (hu : ‖u‖ = 1)
    (hdiff : |f (x + r • u) - f (x - r • u)| ≤ 18 * r) :
    ‖centralDifferenceSignal d f x r u‖ ≤ 9 * d := by
  rw [centralDifferenceSignal, norm_smul, Real.norm_eq_abs, hu, mul_one,
    abs_mul, abs_div, abs_of_nonneg (Nat.cast_nonneg d),
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_pos hr]
  have hcoeff : 0 ≤ (d : ℝ) / (2 * r) := by positivity
  calc
    (d : ℝ) / (2 * r) *
        |f (x + r • u) - f (x - r • u)| ≤
        (d : ℝ) / (2 * r) * (18 * r) :=
      mul_le_mul_of_nonneg_left hdiff hcoeff
    _ = 9 * d := by field_simp [hr.ne']; ring

/-- On the estimator region, the normalized objective has the scalar
central-difference bound used in the pathwise moment calculation. -/
theorem NormalizedObjective.abs_central_difference_le
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (x : Point d) {r : ℝ} (hr : |r| ≤ 1) (u : Point d) (hu : ‖u‖ = 1)
    (hx : ‖x‖ ≤ 1) :
    |F.f (x + r • u) - F.f (x - r • u)| ≤ 18 * |r| := by
  let s : Set (Point d) := closedBall 0 2
  have hplus : x + r • u ∈ s := by
    dsimp only [s]
    rw [mem_closedBall, dist_zero_right]
    calc
      ‖x + r • u‖ ≤ ‖x‖ + ‖r • u‖ := norm_add_le _ _
      _ = ‖x‖ + |r| := by rw [norm_smul, Real.norm_eq_abs, hu, mul_one]
      _ ≤ 2 := by linarith
  have hminus : x - r • u ∈ s := by
    dsimp only [s]
    rw [mem_closedBall, dist_zero_right]
    calc
      ‖x - r • u‖ ≤ ‖x‖ + ‖r • u‖ := norm_sub_le _ _
      _ = ‖x‖ + |r| := by rw [norm_smul, Real.norm_eq_abs, hu, mul_one]
      _ ≤ 2 := by linarith
  have hdiff : Differentiable ℝ F.f :=
    F.smooth.differentiable (by
      norm_cast
      exact Nat.ne_of_gt (lt_of_lt_of_le (by omega : 0 < 2) o.two_le_k))
  have hmv := (convex_closedBall (0 : Point d) 2).norm_image_sub_le_of_norm_fderiv_le
    (fun z _hz ↦ hdiff z)
    (fun z hz ↦ by
      calc
        ‖fderiv ℝ F.f z‖ =
            ‖(InnerProductSpace.toDual ℝ (Point d)).symm (fderiv ℝ F.f z)‖ := by
          symm
          exact (InnerProductSpace.toDual ℝ (Point d)).symm.norm_map _
        _ = ‖∇ F.f z‖ := rfl
        _ ≤ 9 := F.gradient_norm_le_nine
          (show ‖z‖ ≤ 2 by simpa [s, mem_closedBall, dist_zero_right] using hz))
    hplus hminus
  change |F.f (x + r • u) - F.f (x - r • u)| ≤ _
  rw [Real.norm_eq_abs] at hmv
  have hsegment : ‖(x - r • u) - (x + r • u)‖ = 2 * |r| := by
    rw [show (x - r • u) - (x + r • u) = (-2 * r) • u by module,
      norm_smul, Real.norm_eq_abs, hu, mul_one, abs_mul,
      show |-2| = (2 : ℝ) by norm_num]
  rw [hsegment] at hmv
  calc
    |F.f (x + r • u) - F.f (x - r • u)| =
        |F.f (x - r • u) - F.f (x + r • u)| := abs_sub_comm _ _
    _ ≤ 9 * (2 * |r|) := hmv
    _ = 18 * |r| := by ring

/-- The noise-free `β = 4` combination is bounded by `15d` at every unit
direction. -/
theorem NormalizedObjective.norm_betaFourSphericalSignal_le
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (x : Point d) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (u : Point d) (hu : ‖u‖ = 1) (hx : ‖x‖ ≤ 1) :
    ‖betaFourSphericalSignal d F.f x h u‖ ≤ 15 * d := by
  have hOuterDiff := F.abs_central_difference_le x
    (show |h| ≤ 1 by simpa [abs_of_pos hh] using hh1) u hu hx
  have hInnerDiff := F.abs_central_difference_le x
    (show |h / 2| ≤ 1 by
      rw [abs_div, abs_of_pos hh, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith) u hu hx
  have hOuter := norm_centralDifferenceSignal_le d F.f x hh u hu
    (by simpa [abs_of_pos hh] using hOuterDiff)
  have hInner := norm_centralDifferenceSignal_le d F.f x (half_pos hh) u hu
    (by simpa [abs_of_pos hh, abs_of_pos (half_pos hh)] using hInnerDiff)
  calc
    ‖betaFourSphericalSignal d F.f x h u‖ ≤
        ‖(-1 / 3 : ℝ) • centralDifferenceSignal d F.f x h u‖ +
          ‖(4 / 3 : ℝ) • centralDifferenceSignal d F.f x (h / 2) u‖ := by
      exact norm_add_le _ _
    _ = (1 / 3 : ℝ) * ‖centralDifferenceSignal d F.f x h u‖ +
        (4 / 3 : ℝ) * ‖centralDifferenceSignal d F.f x (h / 2) u‖ := by
      simp [norm_smul]
    _ ≤ (1 / 3 : ℝ) * (9 * d) + (4 / 3 : ℝ) * (9 * d) := by gcongr
    _ = 15 * d := by ring

/-- The variance `130 = 8²·2 + 1²·2` of the four-noise scalar combination
gives the exact `65/18` vector-noise second moment.  Independence and Gaussian
moments are used only through the displayed scalar moment premise. -/
theorem integral_norm_betaFourSphericalNoise_sq_eq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (d : ℕ) {h : ℝ} (hh : h ≠ 0) (u : Ω → Point d)
    (ξOuterPlus ξOuterMinus ξInnerPlus ξInnerMinus : Ω → ℝ)
    (hu : ∀ᵐ ω ∂μ, ‖u ω‖ = 1)
    (hscalarMoment :
      (∫ ω, (betaFourNoiseScalar
        (ξOuterPlus ω) (ξOuterMinus ω)
        (ξInnerPlus ω) (ξInnerMinus ω)) ^ 2 ∂μ) = 130) :
    (∫ ω, ‖betaFourSphericalNoise d h (u ω)
        (ξOuterPlus ω) (ξOuterMinus ω)
        (ξInnerPlus ω) (ξInnerMinus ω)‖ ^ 2 ∂μ) =
      65 * d ^ 2 / (18 * h ^ 2) := by
  calc
    (∫ ω, ‖betaFourSphericalNoise d h (u ω)
        (ξOuterPlus ω) (ξOuterMinus ω)
        (ξInnerPlus ω) (ξInnerMinus ω)‖ ^ 2 ∂μ) =
        ∫ ω, ((d : ℝ) / (6 * h)) ^ 2 *
          (betaFourNoiseScalar
            (ξOuterPlus ω) (ξOuterMinus ω)
            (ξInnerPlus ω) (ξInnerMinus ω)) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hu] with ω hunit
      exact norm_betaFourSphericalNoise_sq d hh (u ω) hunit _ _ _ _
    _ = ((d : ℝ) / (6 * h)) ^ 2 * 130 := by
      rw [integral_const_mul, hscalarMoment]
    _ = 65 * d ^ 2 / (18 * h ^ 2) := by
      convert (betaFour_noise_constant (d := (d : ℝ)) (h := h) hh) using 1 <;>
        norm_num

/-- Fresh centered unit-variance noises give the scalar variance `130` once
the inner and outer differences have variance two and are orthogonal. -/
theorem integral_betaFourNoiseScalar_sq_eq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (ξOuterPlus ξOuterMinus ξInnerPlus ξInnerMinus : Ω → ℝ)
    (hinnerSq : Integrable
      (fun ω ↦ (ξInnerPlus ω - ξInnerMinus ω) ^ 2) μ)
    (houterSq : Integrable
      (fun ω ↦ (ξOuterPlus ω - ξOuterMinus ω) ^ 2) μ)
    (hcrossInt : Integrable
      (fun ω ↦ (ξInnerPlus ω - ξInnerMinus ω) *
        (ξOuterPlus ω - ξOuterMinus ω)) μ)
    (hinnerMoment :
      (∫ ω, (ξInnerPlus ω - ξInnerMinus ω) ^ 2 ∂μ) = 2)
    (houterMoment :
      (∫ ω, (ξOuterPlus ω - ξOuterMinus ω) ^ 2 ∂μ) = 2)
    (hcross :
      (∫ ω, (ξInnerPlus ω - ξInnerMinus ω) *
        (ξOuterPlus ω - ξOuterMinus ω) ∂μ) = 0) :
    (∫ ω, (betaFourNoiseScalar
      (ξOuterPlus ω) (ξOuterMinus ω)
      (ξInnerPlus ω) (ξInnerMinus ω)) ^ 2 ∂μ) = 130 := by
  let inner : Ω → ℝ := fun ω ↦ ξInnerPlus ω - ξInnerMinus ω
  let outer : Ω → ℝ := fun ω ↦ ξOuterPlus ω - ξOuterMinus ω
  have hi : Integrable (fun ω ↦ inner ω ^ 2) μ := by
    simpa only [inner] using hinnerSq
  have ho : Integrable (fun ω ↦ outer ω ^ 2) μ := by
    simpa only [outer] using houterSq
  have hc : Integrable (fun ω ↦ inner ω * outer ω) μ := by
    simpa only [inner, outer] using hcrossInt
  calc
    (∫ ω, (betaFourNoiseScalar
        (ξOuterPlus ω) (ξOuterMinus ω)
        (ξInnerPlus ω) (ξInnerMinus ω)) ^ 2 ∂μ) =
        ∫ ω, (64 * inner ω ^ 2 - 16 * (inner ω * outer ω)) +
          outer ω ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards with ω
      dsimp only [inner, outer, betaFourNoiseScalar]
      ring
    _ = (∫ ω, 64 * inner ω ^ 2 - 16 * (inner ω * outer ω) ∂μ) +
        ∫ ω, outer ω ^ 2 ∂μ := by
      exact integral_add ((hi.const_mul 64).sub (hc.const_mul 16)) ho
    _ = ((∫ ω, 64 * inner ω ^ 2 ∂μ) -
        ∫ ω, 16 * (inner ω * outer ω) ∂μ) +
        ∫ ω, outer ω ^ 2 ∂μ := by
      rw [integral_sub (hi.const_mul 64) (hc.const_mul 16)]
    _ = 64 * (∫ ω, inner ω ^ 2 ∂μ) -
        16 * (∫ ω, inner ω * outer ω ∂μ) +
        ∫ ω, outer ω ^ 2 ∂μ := by
      rw [integral_const_mul, integral_const_mul]
    _ = 130 := by
      rw [show (∫ ω, inner ω ^ 2 ∂μ) = 2 by simpa [inner] using hinnerMoment,
        show (∫ ω, outer ω ^ 2 ∂μ) = 2 by simpa [outer] using houterMoment,
        show (∫ ω, inner ω * outer ω ∂μ) = 0 by
          simpa [inner, outer] using hcross]
      norm_num

/-- Exact signal/noise orthogonality plus the pathwise `15d` signal bound
gives the manuscript's `229 d²/h²` second-moment envelope. -/
theorem NormalizedObjective.integral_norm_betaFourSphericalEstimator_sq_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (x : Point d) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (u : Ω → Point d)
    (ξOuterPlus ξOuterMinus ξInnerPlus ξInnerMinus : Ω → ℝ)
    (hu : ∀ᵐ ω ∂μ, ‖u ω‖ = 1)
    (hsignalSq : Integrable
      (fun ω ↦ ‖betaFourSphericalSignal d F.f x h (u ω)‖ ^ 2) μ)
    (hcrossInt : Integrable
      (fun ω ↦ ⟪betaFourSphericalSignal d F.f x h (u ω),
        betaFourSphericalNoise d h (u ω)
          (ξOuterPlus ω) (ξOuterMinus ω)
          (ξInnerPlus ω) (ξInnerMinus ω)⟫_ℝ) μ)
    (hnoiseSq : Integrable
      (fun ω ↦ ‖betaFourSphericalNoise d h (u ω)
        (ξOuterPlus ω) (ξOuterMinus ω)
        (ξInnerPlus ω) (ξInnerMinus ω)‖ ^ 2) μ)
    (hcross :
      (∫ ω, ⟪betaFourSphericalSignal d F.f x h (u ω),
        betaFourSphericalNoise d h (u ω)
          (ξOuterPlus ω) (ξOuterMinus ω)
          (ξInnerPlus ω) (ξInnerMinus ω)⟫_ℝ ∂μ) = 0)
    (hnoiseMoment :
      (∫ ω, ‖betaFourSphericalNoise d h (u ω)
        (ξOuterPlus ω) (ξOuterMinus ω)
        (ξInnerPlus ω) (ξInnerMinus ω)‖ ^ 2 ∂μ) =
          65 * d ^ 2 / (18 * h ^ 2))
    (hx : ‖x‖ ≤ 1) :
    (∫ ω, ‖betaFourSphericalEstimator d F.f x h (u ω)
        (ξOuterPlus ω) (ξOuterMinus ω)
        (ξInnerPlus ω) (ξInnerMinus ω)‖ ^ 2 ∂μ) ≤
      229 * d ^ 2 / h ^ 2 := by
  let signal : Ω → Point d := fun ω ↦ betaFourSphericalSignal d F.f x h (u ω)
  let noise : Ω → Point d := fun ω ↦ betaFourSphericalNoise d h (u ω)
    (ξOuterPlus ω) (ξOuterMinus ω) (ξInnerPlus ω) (ξInnerMinus ω)
  have hsignalBound : ∀ᵐ ω ∂μ, ‖signal ω‖ ^ 2 ≤ 225 * d ^ 2 := by
    filter_upwards [hu] with ω hunit
    have hnorm := F.norm_betaFourSphericalSignal_le x hh hh1 (u ω) hunit hx
    calc
      ‖signal ω‖ ^ 2 ≤ (15 * (d : ℝ)) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm
      _ = 225 * d ^ 2 := by ring
  have hsignalIntegral : ∫ ω, ‖signal ω‖ ^ 2 ∂μ ≤ 225 * d ^ 2 := by
    calc
      ∫ ω, ‖signal ω‖ ^ 2 ∂μ ≤ ∫ _ω, (225 * d ^ 2 : ℝ) ∂μ := by
        apply integral_mono_ae
        · simpa only [signal] using hsignalSq
        · exact integrable_const _
        · exact hsignalBound
      _ = 225 * d ^ 2 := by simp
  have hexpand :
      (∫ ω, ‖betaFourSphericalEstimator d F.f x h (u ω)
        (ξOuterPlus ω) (ξOuterMinus ω)
        (ξInnerPlus ω) (ξInnerMinus ω)‖ ^ 2 ∂μ) =
        (∫ ω, ‖signal ω‖ ^ 2 ∂μ) +
          2 * (∫ ω, ⟪signal ω, noise ω⟫_ℝ ∂μ) +
          (∫ ω, ‖noise ω‖ ^ 2 ∂μ) := by
    have hs : Integrable (fun ω ↦ ‖signal ω‖ ^ 2) μ := by
      simpa only [signal] using hsignalSq
    have hc : Integrable (fun ω ↦ ⟪signal ω, noise ω⟫_ℝ) μ := by
      simpa only [signal, noise] using hcrossInt
    have hn : Integrable (fun ω ↦ ‖noise ω‖ ^ 2) μ := by
      simpa only [noise] using hnoiseSq
    calc
      (∫ ω, ‖betaFourSphericalEstimator d F.f x h (u ω)
          (ξOuterPlus ω) (ξOuterMinus ω)
          (ξInnerPlus ω) (ξInnerMinus ω)‖ ^ 2 ∂μ) =
          ∫ ω, (‖signal ω‖ ^ 2 + 2 * ⟪signal ω, noise ω⟫_ℝ) +
            ‖noise ω‖ ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards with ω
        exact norm_add_sq_real (signal ω) (noise ω)
      _ = (∫ ω, (‖signal ω‖ ^ 2 + 2 * ⟪signal ω, noise ω⟫_ℝ) ∂μ) +
          (∫ ω, ‖noise ω‖ ^ 2 ∂μ) := integral_add (hs.add (hc.const_mul 2)) hn
      _ = ((∫ ω, ‖signal ω‖ ^ 2 ∂μ) +
          ∫ ω, 2 * ⟪signal ω, noise ω⟫_ℝ ∂μ) +
          (∫ ω, ‖noise ω‖ ^ 2 ∂μ) := by rw [integral_add hs (hc.const_mul 2)]
      _ = (∫ ω, ‖signal ω‖ ^ 2 ∂μ) +
          2 * (∫ ω, ⟪signal ω, noise ω⟫_ℝ ∂μ) +
          (∫ ω, ‖noise ω‖ ^ 2 ∂μ) := by rw [integral_const_mul]
  rw [hexpand]
  change (∫ ω, ‖signal ω‖ ^ 2 ∂μ) +
      2 * (∫ ω, ⟪signal ω, noise ω⟫_ℝ ∂μ) +
      (∫ ω, ‖noise ω‖ ^ 2 ∂μ) ≤ _
  rw [show (∫ ω, ⟪signal ω, noise ω⟫_ℝ ∂μ) = 0 by simpa [signal, noise] using hcross,
    show (∫ ω, ‖noise ω‖ ^ 2 ∂μ) = 65 * d ^ 2 / (18 * h ^ 2) by
      simpa [noise] using hnoiseMoment]
  simp only [mul_zero, add_zero]
  calc
    (∫ ω, ‖signal ω‖ ^ 2 ∂μ) + 65 * d ^ 2 / (18 * h ^ 2) ≤
        225 * d ^ 2 + 65 * d ^ 2 / (18 * h ^ 2) :=
      add_le_add hsignalIntegral (le_refl _)
    _ ≤ 229 * d ^ 2 / h ^ 2 := betaFour_secondMoment_envelope hh hh1

/-- Mean of the full estimator after supplying the surface-to-ball identity
for its noise-free part and zero mean of its noise part. -/
theorem integral_betaFourSphericalEstimator_eq_ballField
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (x : Point d) (h : ℝ) (u : Ω → Point d)
    (ξOuterPlus ξOuterMinus ξInnerPlus ξInnerMinus : Ω → ℝ)
    (hsignal : Integrable (fun ω ↦ betaFourSphericalSignal d F.f x h (u ω)) μ)
    (hnoise : Integrable (fun ω ↦ betaFourSphericalNoise d h (u ω)
      (ξOuterPlus ω) (ξOuterMinus ω) (ξInnerPlus ω) (ξInnerMinus ω)) μ)
    (hsmoothing :
      (∫ ω, betaFourSphericalSignal d F.f x h (u ω) ∂μ) =
        betaFourBallField d (∇ F.f) x h)
    (hnoiseMean :
      (∫ ω, betaFourSphericalNoise d h (u ω)
        (ξOuterPlus ω) (ξOuterMinus ω) (ξInnerPlus ω) (ξInnerMinus ω) ∂μ) = 0) :
    (∫ ω, betaFourSphericalEstimator d F.f x h (u ω)
        (ξOuterPlus ω) (ξOuterMinus ω) (ξInnerPlus ω) (ξInnerMinus ω) ∂μ) =
      betaFourBallField d (∇ F.f) x h := by
  rw [show (fun ω ↦ betaFourSphericalEstimator d F.f x h (u ω)
      (ξOuterPlus ω) (ξOuterMinus ω) (ξInnerPlus ω) (ξInnerMinus ω)) =
      (fun ω ↦ betaFourSphericalSignal d F.f x h (u ω) +
        betaFourSphericalNoise d h (u ω)
          (ξOuterPlus ω) (ξOuterMinus ω) (ξInnerPlus ω) (ξInnerMinus ω)) by
    rfl, integral_add hsignal hnoise, hsmoothing, hnoiseMean, add_zero]

/-- The concrete mean identity plus the ball-Taylor theorem yields cubic
bias for the explicit four-query estimator. -/
theorem NormalizedObjective.norm_integral_betaFourSphericalEstimator_sub_gradient_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hbeta : o.beta = 4) (x : Point d) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (u : Ω → Point d)
    (ξOuterPlus ξOuterMinus ξInnerPlus ξInnerMinus : Ω → ℝ)
    (hsignal : Integrable (fun ω ↦ betaFourSphericalSignal d F.f x h (u ω)) μ)
    (hnoise : Integrable (fun ω ↦ betaFourSphericalNoise d h (u ω)
      (ξOuterPlus ω) (ξOuterMinus ω) (ξInnerPlus ω) (ξInnerMinus ω)) μ)
    (hsmoothing :
      (∫ ω, betaFourSphericalSignal d F.f x h (u ω) ∂μ) =
        betaFourBallField d (∇ F.f) x h)
    (hnoiseMean :
      (∫ ω, betaFourSphericalNoise d h (u ω)
        (ξOuterPlus ω) (ξOuterMinus ω) (ξInnerPlus ω) (ξInnerMinus ω) ∂μ) = 0)
    (hx : ‖x‖ ≤ 1) :
    ‖(∫ ω, betaFourSphericalEstimator d F.f x h (u ω)
        (ξOuterPlus ω) (ξOuterMinus ω) (ξInnerPlus ω) (ξInnerMinus ω) ∂μ) -
      ∇ F.f x‖ ≤ h ^ 3 / 12 := by
  rw [integral_betaFourSphericalEstimator_eq_ballField μ F x h u
    ξOuterPlus ξOuterMinus ξInnerPlus ξInnerMinus hsignal hnoise hsmoothing hnoiseMean]
  simpa [abs_of_pos hh] using
    F.norm_betaFourBallField_sub_gradient_le hbeta x h hx
      (by simpa [abs_of_pos hh] using hh1)

end

end NoisyZO
