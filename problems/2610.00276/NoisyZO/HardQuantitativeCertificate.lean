import NoisyZO.RadialProfile

/-!
# Reduced quantitative certificate for the radial hard family

Smoothness, center feasibility, and center stationarity are automatic for the
explicit radial construction once its elementary parameter inequalities are
known.  The strong-convexity and full-gradient bounds both follow from one
unit Lipschitz bound on the localized perturbation gradient.  The remaining
certificate therefore contains only that bound and the highest-derivative
Holder estimate used by the normalized objective class.
-/

open scoped Gradient InnerProductSpace

namespace NoisyZO

noncomputable section

/-- The two genuinely quantitative parts of radial hard-family admissibility. -/
structure RadialHardQuantitativeCertificate
    (o : SmoothnessOrder) (d : ℕ) (c h : ℝ) (hh : 0 < h)
    (s : Hypercube d) where
  perturbation_gradient_lipschitz : ∀ x y,
    ‖∇ (hardPerturbation (radialCutoff d h hh)
        (c / Real.sqrt d) (hypercubeSign s)) x -
      ∇ (hardPerturbation (radialCutoff d h hh)
        (c / Real.sqrt d) (hypercubeSign s)) y‖ ≤ ‖x - y‖
  perturbation_higher_holder : ∀ x y,
    ‖iteratedFDeriv ℝ o.k
        (hardPerturbation (radialCutoff d h hh)
          (c / Real.sqrt d) (hypercubeSign s)) x -
      iteratedFDeriv ℝ o.k
        (hardPerturbation (radialCutoff d h hh)
          (c / Real.sqrt d) (hypercubeSign s)) y‖ ≤
      ‖x - y‖ ^ o.alpha

/-- Dimension-free derivative bounds for the manuscript's unit-scale profile.
The constants `M₂` and `H` are separated from the rescaling arithmetic. -/
structure UnitRadialProfileCertificate
    (o : SmoothnessOrder) (d : ℕ) (s : Hypercube d)
    (M₂ H : ℝ) where
  M₂_nonneg : 0 ≤ M₂
  H_nonneg : 0 ≤ H
  gradient_lipschitz : ∀ u v,
    ‖∇ (normalizedRadialProfile s) u -
      ∇ (normalizedRadialProfile s) v‖ ≤ M₂ * ‖u - v‖
  higher_holder : ∀ u v,
    ‖iteratedFDeriv ℝ o.k (normalizedRadialProfile s) u -
      iteratedFDeriv ℝ o.k (normalizedRadialProfile s) v‖ ≤
        H * ‖u - v‖ ^ o.alpha

/-- Rescale dimension-free unit-profile estimates into the two quantitative
bounds required by the radius-`h` hard family.  All analytic content is in
`profile`; the two other hypotheses are scalar smallness inequalities. -/
theorem radialHardQuantitativeCertificateOfUnitProfile
    {o : SmoothnessOrder} {d : ℕ} (s : Hypercube d)
    (a h M₂ H : ℝ) (hh : 0 < h)
    (profile : UnitRadialProfileCertificate o d s M₂ H)
    (hgradientScale :
      |(-a * h ^ o.beta) * h⁻¹| * M₂ * |h⁻¹| ≤ 1)
    (hhigherScale :
      |(-a * h ^ o.beta) * (h⁻¹ ^ o.k)| * H *
        |h⁻¹| ^ o.alpha ≤ 1) :
    RadialHardQuantitativeCertificate o d
      (a * h ^ (o.beta - 1)) h hh s where
  perturbation_gradient_lipschitz := by
    intro x y
    rw [norm_gradient_hardPerturbation_radialCutoff_sub]
    calc
      |(-a * h ^ o.beta) * h⁻¹| *
          ‖∇ (normalizedRadialProfile s) (h⁻¹ • x) -
            ∇ (normalizedRadialProfile s) (h⁻¹ • y)‖ ≤
        |(-a * h ^ o.beta) * h⁻¹| *
          (M₂ * ‖h⁻¹ • x - h⁻¹ • y‖) :=
        mul_le_mul_of_nonneg_left
          (profile.gradient_lipschitz (h⁻¹ • x) (h⁻¹ • y))
          (abs_nonneg _)
      _ = (|(-a * h ^ o.beta) * h⁻¹| * M₂ * |h⁻¹|) *
          ‖x - y‖ := by
        have hsub : h⁻¹ • x - h⁻¹ • y = h⁻¹ • (x - y) := by module
        rw [hsub, norm_smul, Real.norm_eq_abs]
        ring
      _ ≤ 1 * ‖x - y‖ :=
        mul_le_mul_of_nonneg_right hgradientScale (norm_nonneg _)
      _ = ‖x - y‖ := one_mul _
  perturbation_higher_holder := by
    intro x y
    rw [norm_iteratedFDeriv_hardPerturbation_sub]
    calc
      |(-a * h ^ o.beta) * (h⁻¹ ^ o.k)| *
          ‖iteratedFDeriv ℝ o.k (normalizedRadialProfile s) (h⁻¹ • x) -
            iteratedFDeriv ℝ o.k (normalizedRadialProfile s) (h⁻¹ • y)‖ ≤
        |(-a * h ^ o.beta) * (h⁻¹ ^ o.k)| *
          (H * ‖h⁻¹ • x - h⁻¹ • y‖ ^ o.alpha) :=
        mul_le_mul_of_nonneg_left
          (profile.higher_holder (h⁻¹ • x) (h⁻¹ • y))
          (abs_nonneg _)
      _ = (|(-a * h ^ o.beta) * (h⁻¹ ^ o.k)| * H *
          |h⁻¹| ^ o.alpha) * ‖x - y‖ ^ o.alpha := by
        have hsub : h⁻¹ • x - h⁻¹ • y = h⁻¹ • (x - y) := by module
        rw [hsub, norm_smul, Real.norm_eq_abs,
          Real.mul_rpow (abs_nonneg _) (norm_nonneg _)]
        ring
      _ ≤ 1 * ‖x - y‖ ^ o.alpha :=
        mul_le_mul_of_nonneg_right hhigherScale
          (Real.rpow_nonneg (norm_nonneg _) _)
      _ = ‖x - y‖ ^ o.alpha := one_mul _

/-- The first-order rescaling factor is `a M₂ h^(β-2)`. -/
theorem radial_gradient_scale_factor
    (o : SmoothnessOrder) (a h M₂ : ℝ) (ha : 0 < a) (hh : 0 < h) :
    |(-a * h ^ o.beta) * h⁻¹| * M₂ * |h⁻¹| =
      (a * M₂) * h ^ (o.beta - 2) := by
  rw [abs_mul, abs_mul, abs_neg, abs_of_pos ha,
    abs_of_pos (Real.rpow_pos_of_pos hh _), abs_inv, abs_of_pos hh]
  rw [Real.rpow_sub hh o.beta 2]
  norm_num [div_eq_mul_inv]
  field_simp [hh.ne']

/-- At the smoothness decomposition `β = k + α`, the highest-derivative
rescaling factor is exactly `a H`. -/
theorem radial_higher_scale_factor
    (o : SmoothnessOrder) (a h H : ℝ) (ha : 0 < a) (hh : 0 < h) :
    |(-a * h ^ o.beta) * (h⁻¹ ^ o.k)| * H * |h⁻¹| ^ o.alpha =
      a * H := by
  rw [abs_mul, abs_mul, abs_neg, abs_of_pos ha,
    abs_of_pos (Real.rpow_pos_of_pos hh _), abs_pow, abs_inv,
    abs_of_pos hh]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_neg_eq_inv_rpow]
  rw [← Real.rpow_neg_eq_inv_rpow]
  have hexp : o.beta + -(o.k : ℝ) + -o.alpha = 0 := by
    rw [o.beta_eq]
    ring
  calc
    a * h ^ o.beta * h ^ (-(o.k : ℝ)) * H * h ^ (-o.alpha) =
        a * H * (h ^ o.beta * h ^ (-(o.k : ℝ)) * h ^ (-o.alpha)) := by ring
    _ = a * H * h ^ (o.beta + -(o.k : ℝ) + -o.alpha) := by
      rw [← Real.rpow_add hh o.beta (-(o.k : ℝ)),
        ← Real.rpow_add hh (o.beta + -(o.k : ℝ)) (-o.alpha)]
    _ = a * H := by rw [hexp, Real.rpow_zero, mul_one]

/-- Manuscript-form constructor: dimension-free unit-profile constants and
the small-amplitude conditions `a M₂ ≤ 1`, `a H ≤ 1` imply both remaining
quantitative hard-family bounds for every `0 < h ≤ 1`. -/
theorem radialHardQuantitativeCertificateOfUnitProfileSmall
    {o : SmoothnessOrder} {d : ℕ} (s : Hypercube d)
    (a h M₂ H : ℝ) (ha : 0 < a) (hh : 0 < h) (hh1 : h ≤ 1)
    (profile : UnitRadialProfileCertificate o d s M₂ H)
    (haM₂ : a * M₂ ≤ 1) (haH : a * H ≤ 1) :
    RadialHardQuantitativeCertificate o d
      (a * h ^ (o.beta - 1)) h hh s := by
  apply radialHardQuantitativeCertificateOfUnitProfile
    s a h M₂ H hh profile
  · rw [radial_gradient_scale_factor o a h M₂ ha hh]
    calc
      (a * M₂) * h ^ (o.beta - 2) ≤ (a * M₂) * 1 :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_one hh.le hh1 (by linarith [o.beta_gt_two]))
          (mul_nonneg ha.le profile.M₂_nonneg)
      _ ≤ 1 := by simpa using haM₂
  · rw [radial_higher_scale_factor o a h H ha hh]
    exact haH

/-- Add the automatic smoothness and center geometry to a reduced
quantitative certificate. -/
theorem radialHardAnalyticCertificateOfQuantitative
    {o : SmoothnessOrder} {d : ℕ} (c h : ℝ) (hh : 0 < h)
    (s : Hypercube d)
    (hcenter_mem :
      ‖hardCenter (c / Real.sqrt d) (hypercubeSign s)‖ ≤ 1)
    (hcenter_flat :
      ‖hardCenter (c / Real.sqrt d) (hypercubeSign s)‖ < h / 2)
    (cert : RadialHardQuantitativeCertificate o d c h hh s) :
    HardAnalyticCertificate o d
      (radialCutoff d h hh) (c / Real.sqrt d) (hypercubeSign s) where
  smooth := hardValue_radialCutoff_contDiff
    (c / Real.sqrt d) h hh (hypercubeSign s)
  center_mem := hcenter_mem
  strong := hardValue_strong_of_perturbation
    (c / Real.sqrt d) h hh (hypercubeSign s)
    cert.perturbation_gradient_lipschitz
  gradient_lipschitz := hardValue_gradient_lipschitz_of_perturbation
    (c / Real.sqrt d) h hh (hypercubeSign s)
    cert.perturbation_gradient_lipschitz
  higher_holder := hardValue_higher_holder_of_perturbation
    o.two_le_k o.alpha (c / Real.sqrt d) h hh (hypercubeSign s)
    cert.perturbation_higher_holder
  center_stationary := hardValue_radialCutoff_center_stationary
    h (c / Real.sqrt d) hh (hypercubeSign s) hcenter_flat

/-- In the manuscript's parameter range, a reduced quantitative certificate
is enough to construct the complete hard-family admissibility certificate. -/
theorem rateRadialHardAnalyticCertificate
    {o : SmoothnessOrder} {d : ℕ} (hd : 0 < d)
    (β a h : ℝ) (hβ : 2 < β) (ha : 0 < a) (ha4 : a ≤ 1 / 4)
    (hh : 0 < h) (hh1 : h ≤ 1) (s : Hypercube d)
    (cert : RadialHardQuantitativeCertificate
      o d (a * h ^ (β - 1)) h hh s) :
    HardAnalyticCertificate o d
      (radialCutoff d h hh)
      ((a * h ^ (β - 1)) / Real.sqrt d) (hypercubeSign s) := by
  obtain ⟨hmem, hflat⟩ :=
    rateHardCenter_geometry hd β a h hβ ha ha4 hh hh1 s
  exact radialHardAnalyticCertificateOfQuantitative
    (a * h ^ (β - 1)) h hh s hmem hflat cert

/-- The normalized hard objective built from only the reduced quantitative
certificate in the manuscript's parameter range. -/
def rateRadialHardObjective
    {o : SmoothnessOrder} {d : ℕ} (hd : 0 < d)
    (β a h : ℝ) (hβ : 2 < β) (ha : 0 < a) (ha4 : a ≤ 1 / 4)
    (hh : 0 < h) (hh1 : h ≤ 1) (s : Hypercube d)
    (cert : RadialHardQuantitativeCertificate
      o d (a * h ^ (β - 1)) h hh s) : NormalizedObjective o d :=
  hardNormalizedObjective
    (radialCutoff d h hh)
    ((a * h ^ (β - 1)) / Real.sqrt d) (hypercubeSign s)
    (rateRadialHardAnalyticCertificate hd β a h hβ ha ha4 hh hh1 s cert)

/-- Exact minimizer of the hard objective built from the reduced certificate. -/
theorem rateRadialHardObjective_minimizer
    {o : SmoothnessOrder} {d : ℕ} (hd : 0 < d)
    (β a h : ℝ) (hβ : 2 < β) (ha : 0 < a) (ha4 : a ≤ 1 / 4)
    (hh : 0 < h) (hh1 : h ≤ 1) (s : Hypercube d)
    (cert : RadialHardQuantitativeCertificate
      o d (a * h ^ (β - 1)) h hh s) :
    (rateRadialHardObjective hd β a h hβ ha ha4 hh hh1 s cert).minimizer =
      signCenter ((a * h ^ (β - 1)) / (2 * Real.sqrt d)) s := by
  change hardCenter
    ((a * h ^ (β - 1)) / Real.sqrt d) (hypercubeSign s) = _
  ext i
  simp only [hardCenter_apply, hypercubeSign, signCenter_apply]
  ring

end

end NoisyZO
