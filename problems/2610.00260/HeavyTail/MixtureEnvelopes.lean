import HeavyTail.MixtureEntropy

/-! Explicit analytic envelopes for finite mixtures of exponential densities.
The single integrable envelope proved here discharges the regularity inputs of
the entropy derivative theorem, including at simplex boundary points. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace HeavyTail

variable {ι Ω : Type*} [Fintype ι]

def exponentialComponents (r : ι → Ω → ℝ) (i : ι) (ω : Ω) : ℝ := Real.exp (r i ω)
def logEnvelope (r : ι → Ω → ℝ) (ω : Ω) : ℝ := ∑ i, |r i ω|
def densityEnvelope (r : ι → Ω → ℝ) (ω : Ω) : ℝ := ∑ i, Real.exp (r i ω)
def entropyEnvelope (r : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  (1 + logEnvelope r ω) * densityEnvelope r ω

theorem logEnvelope_nonneg (r : ι → Ω → ℝ) (ω : Ω) : 0 ≤ logEnvelope r ω :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem densityEnvelope_nonneg (r : ι → Ω → ℝ) (ω : Ω) : 0 ≤ densityEnvelope r ω :=
  Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)

theorem entropyEnvelope_nonneg (r : ι → Ω → ℝ) (ω : Ω) : 0 ≤ entropyEnvelope r ω :=
  mul_nonneg (by linarith [logEnvelope_nonneg r ω]) (densityEnvelope_nonneg r ω)

theorem component_log_abs_le (r : ι → Ω → ℝ) (i : ι) (ω : Ω) : |r i ω| ≤ logEnvelope r ω := by
  classical
  exact Finset.single_le_sum (f := fun j => |r j ω|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)

theorem exponential_mixture_bounds (r : ι → Ω → ℝ) {w : ι → ℝ}
    (hw : w ∈ stdSimplex ℝ ι) (ω : Ω) :
    Real.exp (-logEnvelope r ω) ≤ mixtureDensity (exponentialComponents r) w ω ∧
      mixtureDensity (exponentialComponents r) w ω ≤ Real.exp (logEnvelope r ω) := by
  have hcomp (i : ι) : Real.exp (-logEnvelope r ω) ≤ Real.exp (r i ω) ∧
      Real.exp (r i ω) ≤ Real.exp (logEnvelope r ω) := by
    have h := abs_le.mp (component_log_abs_le r i ω)
    exact ⟨Real.exp_le_exp.mpr h.1, Real.exp_le_exp.mpr h.2⟩
  rw [mixtureDensity_eq_sum]
  constructor
  · calc
      _ = ∑ i, w i * Real.exp (-logEnvelope r ω) := by rw [← Finset.sum_mul, hw.2, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hcomp i).1 (hw.1 i))
  · calc
      _ ≤ ∑ i, w i * Real.exp (logEnvelope r ω) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hcomp i).2 (hw.1 i))
      _ = _ := by rw [← Finset.sum_mul, hw.2, one_mul]

theorem abs_log_le_of_exp_bounds {A x : ℝ}
    (hlo : Real.exp (-A) ≤ x) (hhi : x ≤ Real.exp A) : |Real.log x| ≤ A := by
  have hx : 0 < x := (Real.exp_pos _).trans_le hlo
  have hl := Real.log_le_log (Real.exp_pos (-A)) hlo
  have hu := Real.log_le_log hx hhi
  rw [Real.log_exp] at hl hu
  exact abs_le.mpr ⟨hl, hu⟩

theorem exponential_mixture_log_bound (r : ι → Ω → ℝ) {w : ι → ℝ}
    (hw : w ∈ stdSimplex ℝ ι) (ω : Ω) :
    |Real.log (mixtureDensity (exponentialComponents r) w ω)| ≤ logEnvelope r ω :=
  abs_log_le_of_exp_bounds (exponential_mixture_bounds r hw ω).1 (exponential_mixture_bounds r hw ω).2

theorem mixtureLinear_norm_bound {φ : ι → Ω → ℝ} (hφ : ∀ i ω, 0 ≤ φ i ω)
    (ω : Ω) : ‖mixtureLinear φ ω‖ ≤ ∑ i, φ i ω := by
  apply (mixtureLinear φ ω).opNorm_le_bound (Finset.sum_nonneg (fun i _ => hφ i ω))
  intro w
  change ‖mixtureDensity φ w ω‖ ≤ _
  rw [mixtureDensity_eq_sum, Finset.sum_mul]
  calc
    _ ≤ ∑ i, ‖w i * φ i ω‖ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum (fun i _ => by
      rw [norm_mul, Real.norm_eq_abs (φ i ω), abs_of_nonneg (hφ i ω)]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right (norm_le_pi_norm w i) (hφ i ω))

theorem mixtureDensity_difference_bound {φ : ι → Ω → ℝ} (hφ : ∀ i ω, 0 ≤ φ i ω)
    (v w : ι → ℝ) (ω : Ω) :
    ‖mixtureDensity φ v ω - mixtureDensity φ w ω‖ ≤ (∑ i, φ i ω) * ‖v - w‖ := by
  rw [mixtureDensity, mixtureDensity, ← map_sub]
  exact ((mixtureLinear φ ω).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (mixtureLinear_norm_bound hφ ω) (norm_nonneg _))

theorem mul_log_difference_envelope {A x y : ℝ}
    (hx : x ∈ Icc (Real.exp (-A)) (Real.exp A))
    (hy : y ∈ Icc (Real.exp (-A)) (Real.exp A)) :
    ‖y * Real.log y - x * Real.log x‖ ≤ (1 + A) * ‖y - x‖ := by
  apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f' := fun z => Real.log z + 1) _ _ (convex_Icc _ _) hx hy
  · intro z hz
    exact (Real.hasDerivAt_mul_log ((Real.exp_pos _).trans_le hz.1).ne').hasDerivWithinAt
  · intro z hz
    rw [Real.norm_eq_abs]
    exact (abs_add _ _).trans (by
      have h := abs_log_le_of_exp_bounds hz.1 hz.2
      norm_num
      linarith)

theorem exponential_entropy_difference_bound (r : ι → Ω → ℝ) {v w : ι → ℝ}
    (hv : v ∈ stdSimplex ℝ ι) (hw : w ∈ stdSimplex ℝ ι) (ω : Ω) :
    ‖mixtureEntropyIntegrand (exponentialComponents r) v ω -
      mixtureEntropyIntegrand (exponentialComponents r) w ω‖ ≤ entropyEnvelope r ω * ‖v - w‖ := by
  have hm := mul_log_difference_envelope (exponential_mixture_bounds r hw ω)
    (exponential_mixture_bounds r hv ω)
  have hd := mixtureDensity_difference_bound
    (φ := exponentialComponents r) (fun i z => (Real.exp_pos _).le) v w ω
  have hA : 0 ≤ 1 + logEnvelope r ω := by linarith [logEnvelope_nonneg r ω]
  change _ ≤ (1 + logEnvelope r ω) * densityEnvelope r ω * ‖v - w‖
  exact hm.trans (by simpa only [densityEnvelope, exponentialComponents, mul_assoc] using
    mul_le_mul_of_nonneg_left hd hA)

theorem exponential_entropy_integrand_bound (r : ι → Ω → ℝ) {w : ι → ℝ}
    (hw : w ∈ stdSimplex ℝ ι) (ω : Ω) :
    ‖mixtureEntropyIntegrand (exponentialComponents r) w ω‖ ≤ entropyEnvelope r ω := by
  have hmass : mixtureDensity (exponentialComponents r) w ω ≤ densityEnvelope r ω := by
    rw [mixtureDensity_eq_sum]
    apply Finset.sum_le_sum
    intro i _
    have hwi : w i ≤ 1 := mem_Icc_of_mem_stdSimplex hw i |>.2
    exact (mul_le_mul_of_nonneg_right hwi (Real.exp_pos _).le).trans_eq (one_mul _)
  have hpos := mixtureDensity_pos (φ := exponentialComponents r) (fun i z => Real.exp_pos _) hw ω
  unfold mixtureEntropyIntegrand entropyEnvelope
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hpos]
  have hlog := exponential_mixture_log_bound r hw ω
  calc
    _ ≤ densityEnvelope r ω * logEnvelope r ω :=
      mul_le_mul hmass hlog (abs_nonneg _) (densityEnvelope_nonneg r ω)
    _ ≤ _ := by nlinarith [densityEnvelope_nonneg r ω]

theorem exponential_entropy_differential_bound (r : ι → Ω → ℝ) {w : ι → ℝ}
    (hw : w ∈ stdSimplex ℝ ι) (ω : Ω) :
    ‖mixtureEntropyDifferential (exponentialComponents r) w ω‖ ≤ entropyEnvelope r ω := by
  have hlog : |Real.log (mixtureDensity (exponentialComponents r) w ω) + 1| ≤
      1 + logEnvelope r ω := by
    have h := abs_add (Real.log (mixtureDensity (exponentialComponents r) w ω)) 1
    have hg := exponential_mixture_log_bound r hw ω
    norm_num at h
    linarith
  unfold mixtureEntropyDifferential entropyEnvelope
  rw [norm_smul (Real.log (mixtureDensity (exponentialComponents r) w ω) + 1)
    (mixtureLinear (exponentialComponents r) ω), Real.norm_eq_abs]
  exact mul_le_mul hlog (mixtureLinear_norm_bound (fun i z => (Real.exp_pos (r i z)).le) ω)
    (norm_nonneg _) (by linarith [logEnvelope_nonneg r ω])

theorem exponential_entropy_regular [MeasurableSpace Ω] {μ : Measure Ω} {r : ι → Ω → ℝ}
    (hr : ∀ i, Measurable (r i)) (hB : Integrable (entropyEnvelope r) μ)
    {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι) :
    Integrable (mixtureEntropyIntegrand (exponentialComponents r) w) μ ∧
    Integrable (mixtureEntropyDifferential (exponentialComponents r) w) μ := by
  have hm := mixtureDensity_measurable (fun i => (hr i).exp) w
  constructor
  · apply hB.mono' _ (Filter.Eventually.of_forall (exponential_entropy_integrand_bound r hw))
    exact (Real.continuous_mul_log.measurable.comp hm).aestronglyMeasurable
  · apply hB.mono' _ (Filter.Eventually.of_forall (exponential_entropy_differential_bound r hw))
    have hlinear : StronglyMeasurable (mixtureLinear (exponentialComponents r)) := by
      apply Finset.stronglyMeasurable_sum
      intro i _
      exact (hr i).exp.stronglyMeasurable.smul stronglyMeasurable_const
    exact ((hm.log.add_const 1).stronglyMeasurable.smul hlinear).aestronglyMeasurable

end HeavyTail
