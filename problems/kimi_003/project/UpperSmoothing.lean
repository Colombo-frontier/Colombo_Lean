import ModelFull

/-!
Population objective and actual normalized-volume ball smoothing for task006.
The moment, measurability and convexity premises are the sample-instance fields;
none of the smoothing conclusions is a field of the model.
-/

open MeasureTheory Metric Set
open scoped BigOperators ENNReal NNReal

namespace Task006.Full

namespace SampleInstance

variable {d : ℕ} {L R : ℝ} {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] (I : SampleInstance d L R Ω μ)

theorem integrable_modulus : Integrable I.modulus μ := by
  have hmeas := I.measurable_modulus.aestronglyMeasurable (μ := μ)
  have hm : Integrable (fun ω => ‖I.modulus ω‖ ^ (3 / 2 : ℝ)) μ := by
    apply (integrable_congr ?_).mpr I.integrable_moment
    filter_upwards [I.nonneg_modulus] with ω hω
    simp only [Real.norm_eq_abs, abs_of_nonneg hω]
  have h₁ := integrable_norm_rpow_of_le hmeas (p := 1) (q := (3 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) hm
  apply (integrable_norm_iff hmeas).mp
  simpa only [Real.rpow_one] using h₁

theorem mean_modulus_le (hL : 0 ≤ L) : (∫ ω, I.modulus ω ∂μ) ≤ L := by
  have hj := (convexOn_rpow (p := (3 / 2 : ℝ)) (by norm_num)).map_integral_le
    (Real.continuous_rpow_const (q := (3 / 2 : ℝ)) (by norm_num)).continuousOn
    isClosed_Ici I.nonneg_modulus I.integrable_modulus I.integrable_moment
  exact (Real.rpow_le_rpow_iff (integral_nonneg_of_ae I.nonneg_modulus) hL
    (by norm_num : 0 < (3 / 2 : ℝ))).mp (hj.trans I.moment_bound)

theorem integrable_sample (hR : 0 ≤ R) {x : Space d} (hx : x ∈ queryDomain d R) :
    Integrable (I.sample x) μ := by
  have hzero : (0 : Space d) ∈ queryDomain d R := by
    simp only [queryDomain, mem_closedBall, dist_self]
    linarith
  refine (I.integrable_origin.abs.add (I.integrable_modulus.mul_const ‖x‖)).mono'
    (I.measurable_sample x hx).aestronglyMeasurable ?_
  filter_upwards [I.lipschitz_sample] with ω hω
  have hp := hω x hx 0 hzero
  simp only [sub_zero] at hp
  rw [Real.norm_eq_abs]
  calc
    |I.sample x ω| = |(I.sample x ω - I.sample 0 ω) + I.sample 0 ω| := by congr 1; ring
    _ ≤ |I.sample x ω - I.sample 0 ω| + |I.sample 0 ω| := abs_add_le _ _
    _ ≤ |I.sample 0 ω| + I.modulus ω * ‖x‖ := by linarith

theorem objective_lipschitz (hL : 0 ≤ L) (hR : 0 ≤ R)
    {x y : Space d} (hx : x ∈ queryDomain d R) (hy : y ∈ queryDomain d R) :
    |I.objective x - I.objective y| ≤ L * ‖x - y‖ := by
  have hix := I.integrable_sample hR hx
  have hiy := I.integrable_sample hR hy
  unfold objective
  rw [← integral_sub hix hiy]
  calc
    |∫ ω, I.sample x ω - I.sample y ω ∂μ| ≤
        ∫ ω, |I.sample x ω - I.sample y ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, I.modulus ω * ‖x - y‖ ∂μ :=
      integral_mono_ae (hix.sub hiy).abs (I.integrable_modulus.mul_const _)
        (I.lipschitz_sample.mono (fun ω hω => hω x hx y hy))
    _ = (∫ ω, I.modulus ω ∂μ) * ‖x - y‖ := integral_mul_const _ _
    _ ≤ L * ‖x - y‖ := mul_le_mul_of_nonneg_right (I.mean_modulus_le hL) (norm_nonneg _)

theorem objective_lipschitzOn (hL : 0 ≤ L) (hR : 0 ≤ R) :
    LipschitzOnWith ⟨L, hL⟩ I.objective (queryDomain d R) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  change ‖I.objective x - I.objective y‖ ≤ L * ‖x - y‖
  rw [Real.norm_eq_abs]
  exact I.objective_lipschitz hL hR hx hy

theorem objective_convex (hR : 0 ≤ R) : ConvexOn ℝ (queryDomain d R) I.objective := by
  refine ⟨convex_closedBall _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz : a • x + b • y ∈ queryDomain d R :=
    (convex_closedBall (0 : Space d) (2 * R)) hx hy ha hb hab
  have hix := I.integrable_sample hR hx
  have hiy := I.integrable_sample hR hy
  have hiz := I.integrable_sample hR hz
  have hpoint : ∀ᵐ ω ∂μ, I.sample (a • x + b • y) ω ≤
      a * I.sample x ω + b * I.sample y ω := by
    filter_upwards [I.convex_sample] with ω hω
    exact hω.2 hx hy ha hb hab
  calc
    I.objective (a • x + b • y) ≤
        ∫ ω, a * I.sample x ω + b * I.sample y ω ∂μ :=
      integral_mono_ae hiz ((hix.const_mul a).add (hiy.const_mul b)) hpoint
    _ = a • I.objective x + b • I.objective y := by
      rw [integral_add (hix.const_mul a) (hiy.const_mul b)]
      simp only [integral_const_mul, smul_eq_mul, objective]

end SampleInstance

/-- The uniform law used by the actual algorithm, from normalized volume on the
unit closed Euclidean ball. Boundary measure zero will identify open-ball law. -/
noncomputable def unitBallLaw (d : ℕ) : Measure (Space d) :=
  (volume (closedBall (0 : Space d) 1))⁻¹ • volume.restrict (closedBall (0 : Space d) 1)

instance unitBallLaw_probability (d : ℕ) : IsProbabilityMeasure (unitBallLaw d) where
  measure_univ := by
    simp only [unitBallLaw, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel (measure_closedBall_pos volume (0 : Space d) zero_lt_one).ne'
      measure_closedBall_lt_top.ne

theorem unitBallLaw_norm_le (d : ℕ) : ∀ᵐ u ∂unitBallLaw d, ‖u‖ ≤ 1 := by
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with u hu
  simpa using hu

/-- Actual spatial smoothing, retaining the exact uniform-ball distribution. -/
noncomputable def ballSmooth {d : ℕ} (f : Space d → ℝ) (ρ : ℝ) (x : Space d) : ℝ :=
  ∫ u, f (x + ρ • u) ∂unitBallLaw d

theorem ballTranslate_mem_queryDomain {d : ℕ} {R ρ : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ ≤ R)
    {x u : Space d} (hx : ‖x‖ ≤ R) (hu : ‖u‖ ≤ 1) :
    x + ρ • u ∈ queryDomain d R := by
  have hru : ‖ρ • u‖ ≤ ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ]
    nlinarith
  change dist (x + ρ • u) 0 ≤ 2 * R
  rw [dist_zero_right]
  have := norm_add_le x (ρ • u)
  linarith

theorem ballSmooth_integrable {d : ℕ} {f : Space d → ℝ} {R ρ : ℝ}
    (hf : ContinuousOn f (queryDomain d R)) (hρ : 0 ≤ ρ) (hρR : ρ ≤ R)
    {x : Space d} (hx : ‖x‖ ≤ R) :
    Integrable (fun u => f (x + ρ • u)) (unitBallLaw d) := by
  have hcont : ContinuousOn (fun u => f (x + ρ • u)) (closedBall (0 : Space d) 1) := by
    apply hf.comp (by fun_prop : Continuous (fun u : Space d => x + ρ • u)).continuousOn
    intro u hu
    exact ballTranslate_mem_queryDomain hρ hρR hx (by simpa using hu)
  have hi := hcont.integrableOn_compact (μ := volume) (isCompact_closedBall (0 : Space d) 1)
  exact hi.smul_measure (ENNReal.inv_ne_top.mpr
    (measure_closedBall_pos volume (0 : Space d) zero_lt_one).ne')

/-- U1 for the exact normalized-volume smoothing of any locally Lipschitz
population objective. Integrability is derived from continuity on the ball. -/
theorem ballSmooth_error {d : ℕ} {f : Space d → ℝ} {R ρ : ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C f (queryDomain d R)) (hρ : 0 ≤ ρ) (hρR : ρ ≤ R)
    {x : Space d} (hx : ‖x‖ ≤ R) :
    |ballSmooth f ρ x - f x| ≤ ρ * C := by
  have hi := ballSmooth_integrable hf.continuousOn hρ hρR hx
  have hzero : x ∈ queryDomain d R := by
    change dist x 0 ≤ 2 * R
    rw [dist_zero_right]
    linarith
  have hpoint : ∀ᵐ u ∂unitBallLaw d, ‖f (x + ρ • u) - f x‖ ≤ ρ * C := by
    filter_upwards [unitBallLaw_norm_le d] with u hu
    have hq := hf.norm_sub_le (ballTranslate_mem_queryDomain hρ hρR hx hu) hzero
    have hid : x + ρ • u - x = ρ • u := by abel
    rw [hid] at hq
    have hru : ‖ρ • u‖ ≤ ρ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ]
      nlinarith
    exact hq.trans (by nlinarith [C.coe_nonneg])
  have hb := norm_integral_le_of_norm_le_const hpoint
  have hconst : (∫ _u : Space d, f x ∂unitBallLaw d) = f x := by simp
  rw [ballSmooth, ← hconst, ← integral_sub hi (integrable_const _)]
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hb

theorem ballSmooth_lipschitz {d : ℕ} {f : Space d → ℝ} {R ρ : ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C f (queryDomain d R)) (hρ : 0 ≤ ρ) (hρR : ρ ≤ R) :
    LipschitzOnWith C (ballSmooth f ρ) (closedBall (0 : Space d) R) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hxn : ‖x‖ ≤ R := by simpa using hx
  have hyn : ‖y‖ ≤ R := by simpa using hy
  have hix := ballSmooth_integrable hf.continuousOn hρ hρR hxn
  have hiy := ballSmooth_integrable hf.continuousOn hρ hρR hyn
  have hpoint : ∀ᵐ u ∂unitBallLaw d,
      ‖f (x + ρ • u) - f (y + ρ • u)‖ ≤ C * ‖x - y‖ := by
    filter_upwards [unitBallLaw_norm_le d] with u hu
    have hq := hf.norm_sub_le (ballTranslate_mem_queryDomain hρ hρR hxn hu)
      (ballTranslate_mem_queryDomain hρ hρR hyn hu)
    simpa only [add_sub_add_right_eq_sub] using hq
  have hb := norm_integral_le_of_norm_le_const hpoint
  change |ballSmooth f ρ x - ballSmooth f ρ y| ≤ C * dist x y
  rw [ballSmooth, ballSmooth, ← integral_sub hix hiy, dist_eq_norm]
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hb

theorem ballSmooth_convex {d : ℕ} {f : Space d → ℝ} {R ρ : ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C f (queryDomain d R))
    (hc : ConvexOn ℝ (queryDomain d R) f) (hρ : 0 ≤ ρ) (hρR : ρ ≤ R) :
    ConvexOn ℝ (closedBall (0 : Space d) R) (ballSmooth f ρ) := by
  refine ⟨convex_closedBall _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxn : ‖x‖ ≤ R := by simpa using hx
  have hyn : ‖y‖ ≤ R := by simpa using hy
  have hz : ‖a • x + b • y‖ ≤ R := by
    simpa using (convex_closedBall (0 : Space d) R) hx hy ha hb hab
  have hix := ballSmooth_integrable hf.continuousOn hρ hρR hxn
  have hiy := ballSmooth_integrable hf.continuousOn hρ hρR hyn
  have hiz := ballSmooth_integrable hf.continuousOn hρ hρR hz
  have hpoint : ∀ᵐ u ∂unitBallLaw d, f (a • x + b • y + ρ • u) ≤
      a * f (x + ρ • u) + b * f (y + ρ • u) := by
    filter_upwards [unitBallLaw_norm_le d] with u hu
    have hq := hc.2 (ballTranslate_mem_queryDomain hρ hρR hxn hu)
      (ballTranslate_mem_queryDomain hρ hρR hyn hu) ha hb hab
    have hid : a • (x + ρ • u) + b • (y + ρ • u) = a • x + b • y + ρ • u := by
      calc
        _ = a • x + b • y + (a • (ρ • u) + b • (ρ • u)) := by
          rw [smul_add, smul_add]
          abel
        _ = _ := by rw [← add_smul, hab, one_smul]
    simpa only [hid, smul_eq_mul] using hq
  unfold ballSmooth
  have hm := integral_mono_ae hiz ((hix.const_mul a).add (hiy.const_mul b)) hpoint
  have heq := integral_add (hix.const_mul a) (hiy.const_mul b)
  simp only [Pi.add_apply] at hm heq
  rw [heq, integral_const_mul, integral_const_mul] at hm
  exact hm

#print axioms SampleInstance.mean_modulus_le
#print axioms SampleInstance.objective_convex
#print axioms ballSmooth_error
#print axioms ballSmooth_convex

end Task006.Full
