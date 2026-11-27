import UpperSmoothing

/-! Exact central-difference calculus, with the manuscript's factor one-half. -/

open MeasureTheory Set
open scoped Interval NNReal

namespace Task006.Full

theorem integral_abs_symmetric {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫ t in -δ..δ, |t|) = δ ^ 2 := by
  have hn : (∫ t in -δ..0, |t|) = δ ^ 2 / 2 := by
    calc
      (∫ t in -δ..0, |t|) = ∫ t in -δ..0, -t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by linarith : -δ ≤ 0)] at ht
        exact abs_of_nonpos ht.2
      _ = δ ^ 2 / 2 := by rw [intervalIntegral.integral_neg, integral_id]; ring
  have hp : (∫ t in 0..δ, |t|) = δ ^ 2 / 2 := by
    calc
      (∫ t in 0..δ, |t|) = ∫ t in 0..δ, t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hδ] at ht
        exact abs_of_nonneg ht.1
      _ = δ ^ 2 / 2 := by rw [integral_id]; ring
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_abs.intervalIntegrable (-δ) 0) (continuous_abs.intervalIntegrable 0 δ), hn, hp]
  ring

/-- The actual scalar central secant. -/
noncomputable def scalarCentralSecant (φ : ℝ → ℝ) (δ : ℝ) : ℝ :=
  (φ δ - φ (-δ)) / (2 * δ)

/-- A Lipschitz derivative gives the precise central-difference error `K δ / 2`,
proved by the fundamental theorem of calculus and the integral of `|t|`. -/
theorem scalarCentralSecant_error {φ φ' : ℝ → ℝ} {δ K : ℝ}
    (hδ : 0 < δ) (hK : 0 ≤ K)
    (hderiv : ∀ t ∈ Icc (-δ) δ, HasDerivAt φ (φ' t) t)
    (hcont : ContinuousOn φ' (Icc (-δ) δ))
    (hvar : ∀ t ∈ Icc (-δ) δ, |φ' t - φ' 0| ≤ K * |t|) :
    |scalarCentralSecant φ δ - φ' 0| ≤ K * δ / 2 := by
  have horder : -δ ≤ δ := by linarith
  have hint := hcont.intervalIntegrable_of_Icc (μ := volume) horder
  have hftc : (∫ t in -δ..δ, φ' t) = φ δ - φ (-δ) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hderiv t ((uIcc_of_le horder) ▸ ht)) hint
  have hdom : ∀ᵐ t : ℝ, t ∈ Ioc (-δ) δ → ‖φ' t - φ' 0‖ ≤ K * |t| := by
    exact ae_of_all _ (fun t ht => by
      simpa only [Real.norm_eq_abs] using hvar t ⟨le_of_lt ht.1, ht.2⟩)
  have hb := intervalIntegral.norm_integral_le_of_norm_le horder hdom
    ((continuous_const.mul continuous_abs).intervalIntegrable (-δ) δ)
  rw [intervalIntegral.integral_const_mul, integral_abs_symmetric hδ.le,
    intervalIntegral.integral_sub hint intervalIntegrable_const,
    hftc, intervalIntegral.integral_const] at hb
  simp only [sub_neg_eq_add, smul_eq_mul, Real.norm_eq_abs] at hb
  have hid : scalarCentralSecant φ δ - φ' 0 =
      (φ δ - φ (-δ) - (δ + δ) * φ' 0) / (2 * δ) := by
    unfold scalarCentralSecant
    field_simp [hδ.ne']
    <;> ring
  rw [hid, abs_div, abs_of_pos (by positivity : 0 < 2 * δ)]
  apply (div_le_iff₀ (by positivity : 0 < 2 * δ)).mpr
  nlinarith

noncomputable def centralSecant {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : E → ℝ) (x q : E) (δ : ℝ) : ℝ :=
  (f (x + δ • q) - f (x - δ • q)) / (2 * δ)

/-- The multidimensional U2 estimate, retaining the exact one-half constant.
The derivative and Lipschitz-gradient hypotheses will be discharged by the
actual uniform-ball convolution theorem. -/
theorem centralSecant_error {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {grad : E → E} {S : Set E} {x q : E} {δ : ℝ} {K : ℝ≥0}
    (hδ : 0 < δ) (hq : ‖q‖ ≤ 1) (hglip : LipschitzOnWith K grad S)
    (hderiv : ∀ y ∈ S, HasFDerivAt f (innerSL ℝ (grad y)) y)
    (hpath : ∀ t ∈ Icc (-δ) δ, x + t • q ∈ S) :
    |centralSecant f x q δ - inner ℝ (grad x) q| ≤ K * δ / 2 := by
  have hx : x ∈ S := by simpa using hpath 0 ⟨by linarith, by linarith⟩
  have hdc : ∀ t ∈ Icc (-δ) δ, HasDerivAt (fun t => f (x + t • q))
      (inner ℝ (grad (x + t • q)) q) t := by
    intro t ht
    have hline : HasDerivAt (fun t : ℝ => x + t • q) q t := by
      simpa using ((hasDerivAt_id t).smul_const q).const_add x
    convert! HasFDerivAt.comp_hasDerivAt t (hderiv _ (hpath t ht)) hline using 1
  have hcont : ContinuousOn (fun t => inner ℝ (grad (x + t • q)) q) (Icc (-δ) δ) :=
    (hglip.continuousOn.comp
      (by fun_prop : Continuous (fun t : ℝ => x + t • q)).continuousOn hpath).inner
        continuousOn_const
  have hvar : ∀ t ∈ Icc (-δ) δ,
      |inner ℝ (grad (x + t • q)) q - inner ℝ (grad (x + (0 : ℝ) • q)) q| ≤ K * |t| := by
    intro t ht
    simp only [zero_smul, add_zero]
    have hdisp : x + t • q - x = t • q := by abel
    have hgrad := hglip.norm_sub_le (hpath t ht) hx
    rw [hdisp, norm_smul, Real.norm_eq_abs] at hgrad
    rw [← inner_sub_left]
    calc
      |inner ℝ (grad (x + t • q) - grad x) q| ≤
          ‖grad (x + t • q) - grad x‖ * ‖q‖ := abs_real_inner_le_norm _ _
      _ ≤ K * |t| := by
        have h₁ := mul_le_mul_of_nonneg_right hgrad (norm_nonneg q)
        have h₂ := mul_le_mul_of_nonneg_left hq (mul_nonneg K.coe_nonneg (abs_nonneg t))
        have h₃ := mul_le_mul_of_nonneg_right h₂ (norm_nonneg q)
        nlinarith [K.coe_nonneg, abs_nonneg t, norm_nonneg q]
  have hs := scalarCentralSecant_error hδ K.coe_nonneg hdc hcont hvar
  simpa only [scalarCentralSecant, centralSecant, zero_smul, add_zero,
    neg_smul, sub_eq_add_neg] using hs

namespace SampleInstance

variable {d : ℕ} {L R : ℝ} {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] (I : SampleInstance d L R Ω μ)

/-- Exactly the two-value secant from one fresh sample handle and one smoothing
vector. Additive reassociation puts its query points in smoothing form. -/
noncomputable def oracleSecant (ρ δ : ℝ) (x q u : Space d) (ω : Ω) : ℝ :=
  (I.sample (x + δ • q + ρ • u) ω - I.sample (x - δ • q + ρ • u) ω) / (2 * δ)

theorem oracleSecant_abs_le_modulus {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ ≤ R)
    (hδ : 0 < δ) {x q u : Space d} (hq : ‖q‖ ≤ 1) (hu : ‖u‖ ≤ 1)
    (hxp : ‖x + δ • q‖ ≤ R) (hxm : ‖x - δ • q‖ ≤ R) :
    ∀ᵐ ω ∂μ, |I.oracleSecant ρ δ x q u ω| ≤ I.modulus ω := by
  filter_upwards [I.nonneg_modulus, I.lipschitz_sample] with ω hG hLip
  have hp := hLip _ (ballTranslate_mem_queryDomain hρ hρR hxp hu)
    _ (ballTranslate_mem_queryDomain hρ hρR hxm hu)
  have hid : (x + δ • q + ρ • u) - (x - δ • q + ρ • u) = (2 * δ) • q := by
    rw [two_mul, add_smul]
    abel
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * δ)] at hp
  rw [oracleSecant, abs_div, abs_of_pos (by positivity : 0 < 2 * δ)]
  apply (div_le_iff₀ (by positivity : 0 < 2 * δ)).mpr
  calc
    |I.sample (x + δ • q + ρ • u) ω - I.sample (x - δ • q + ρ • u) ω| ≤
        I.modulus ω * (2 * δ * ‖q‖) := hp
    _ ≤ I.modulus ω * (2 * δ) := by
      have hm := mul_le_mul_of_nonneg_left hq
        (mul_nonneg hG (show 0 ≤ 2 * δ by positivity))
      nlinarith

theorem oracleSecant_integrable_sample {ρ δ : ℝ} (hR : 0 ≤ R)
    (hρ : 0 ≤ ρ) (hρR : ρ ≤ R) {x q u : Space d} (hu : ‖u‖ ≤ 1)
    (hxp : ‖x + δ • q‖ ≤ R) (hxm : ‖x - δ • q‖ ≤ R) :
    Integrable (I.oracleSecant ρ δ x q u) μ :=
  ((I.integrable_sample hR (ballTranslate_mem_queryDomain hρ hρR hxp hu)).sub
    (I.integrable_sample hR (ballTranslate_mem_queryDomain hρ hρR hxm hu))).div_const _

/-- Averaging the exact sample secant gives the central secant of the actual
ball-smoothed population objective. This is an iterated expectation identity;
the iid sampling implementation supplies this iterated law. -/
theorem oracleSecant_iterated_mean {ρ δ : ℝ} (hL : 0 ≤ L)
    (hρ : 0 ≤ ρ) (hρR : ρ ≤ R) {x q : Space d}
    (hxp : ‖x + δ • q‖ ≤ R) (hxm : ‖x - δ • q‖ ≤ R) :
    (∫ u, (∫ ω, I.oracleSecant ρ δ x q u ω ∂μ) ∂unitBallLaw d) =
      centralSecant (ballSmooth I.objective ρ) x q δ := by
  have hR : 0 ≤ R := hρ.trans hρR
  have hip := ballSmooth_integrable (I.objective_lipschitzOn hL hR).continuousOn hρ hρR hxp
  have him := ballSmooth_integrable (I.objective_lipschitzOn hL hR).continuousOn hρ hρR hxm
  have heq : (fun u => ∫ ω, I.oracleSecant ρ δ x q u ω ∂μ) =ᵐ[unitBallLaw d]
      fun u => (I.objective (x + δ • q + ρ • u) -
        I.objective (x - δ • q + ρ • u)) / (2 * δ) := by
    filter_upwards [unitBallLaw_norm_le d] with u hu
    unfold oracleSecant objective
    rw [integral_div, integral_sub
      (I.integrable_sample hR (ballTranslate_mem_queryDomain hρ hρR hxp hu))
      (I.integrable_sample hR (ballTranslate_mem_queryDomain hρ hρR hxm hu))]
  rw [integral_congr_ae heq, integral_div, integral_sub hip him]
  rfl

end SampleInstance

#print axioms scalarCentralSecant_error
#print axioms centralSecant_error
#print axioms SampleInstance.oracleSecant_iterated_mean

end Task006.Full
