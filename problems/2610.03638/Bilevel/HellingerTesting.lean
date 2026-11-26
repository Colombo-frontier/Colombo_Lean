import Mathlib.MeasureTheory.Function.L2Space

/-!
# Hellinger affinity and randomized testing

All quantities below are actual Bochner integrals of densities with respect to
an arbitrary common measure. No total-variation or testing lower bound is
assumed as a premise.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Bilevel.HellingerTesting

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

def affinity (p q : Ω → ℝ) (ν : Measure Ω) : ℝ :=
  ∫ ω, Real.sqrt (p ω) * Real.sqrt (q ω) ∂ν

theorem affinity_eq_integral_sqrt (p q : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) :
    affinity p q ν = ∫ ω, Real.sqrt (p ω * q ω) ∂ν := by
  simp only [affinity, Real.sqrt_mul (hp _)]

theorem sqrt_memLp (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hi : Integrable p ν) :
    MemLp (fun ω => Real.sqrt (p ω)) 2 ν := by
  apply (memLp_two_iff_integrable_sq
    (Real.continuous_sqrt.comp_aestronglyMeasurable hi.aestronglyMeasurable)).mpr
  simpa only [Real.sq_sqrt (hp _)] using hi

theorem cauchy_schwarz_nonneg (f g : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) (hg : ∀ ω, 0 ≤ g ω)
    (hflp : MemLp f 2 ν) (hglp : MemLp g 2 ν) :
    (∫ ω, f ω * g ω ∂ν) ≤
      Real.sqrt (∫ ω, f ω ^ 2 ∂ν) * Real.sqrt (∫ ω, g ω ^ 2 ∂ν) := by
  have hc : Real.HolderConjugate 2 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hc
    (Filter.Eventually.of_forall hf) (Filter.Eventually.of_forall hg)
    (by simpa using hflp) (by simpa using hglp)
  simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using h

theorem affinity_nonneg (p q : Ω → ℝ) : 0 ≤ affinity p q ν :=
  integral_nonneg (fun _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

theorem affinity_le_one (p q : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hq : ∀ ω, 0 ≤ q ω)
    (hip : Integrable p ν) (hiq : Integrable q ν)
    (hnp : ∫ ω, p ω ∂ν = 1) (hnq : ∫ ω, q ω ∂ν = 1) : affinity p q ν ≤ 1 := by
  have h := cauchy_schwarz_nonneg (fun ω => Real.sqrt (p ω)) (fun ω => Real.sqrt (q ω))
    (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)
    (sqrt_memLp p hp hip) (sqrt_memLp q hq hiq)
  simpa only [Real.sq_sqrt (hp _), Real.sq_sqrt (hq _), hnp, hnq, Real.sqrt_one,
    one_mul, affinity] using h

/-- The sharp Hellinger-to-total-variation inequality for normalized densities. -/
theorem integral_abs_sub_le (p q : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hq : ∀ ω, 0 ≤ q ω)
    (hip : Integrable p ν) (hiq : Integrable q ν)
    (hnp : ∫ ω, p ω ∂ν = 1) (hnq : ∫ ω, q ω ∂ν = 1) :
    (∫ ω, |p ω - q ω| ∂ν) ≤ 2 * Real.sqrt (1 - affinity p q ν ^ 2) := by
  let u := fun ω => |Real.sqrt (p ω) - Real.sqrt (q ω)|
  let v := fun ω => Real.sqrt (p ω) + Real.sqrt (q ω)
  have hplp := sqrt_memLp p hp hip
  have hqlp := sqrt_memLp q hq hiq
  have hprod : Integrable (fun ω => Real.sqrt (p ω) * Real.sqrt (q ω)) ν :=
    hplp.integrable_mul hqlp
  have hsum : Integrable (fun ω => p ω + q ω) ν := hip.add hiq
  have hu : MemLp u 2 ν := by
    simpa only [u, Real.norm_eq_abs] using (hplp.sub hqlp).norm
  have hv : MemLp v 2 ν := hplp.add hqlp
  have hu2 : (∫ ω, u ω ^ 2 ∂ν) = 2 - 2 * affinity p q ν := by
    calc
      _ = ∫ ω, (p ω + q ω) - 2 * (Real.sqrt (p ω) * Real.sqrt (q ω)) ∂ν := by
        apply integral_congr_ae
        filter_upwards [] with ω
        dsimp [u]
        rw [sq_abs]
        nlinarith [Real.sq_sqrt (hp ω), Real.sq_sqrt (hq ω)]
      _ = _ := by
        rw [integral_sub hsum (hprod.const_mul 2), integral_add hip hiq,
          integral_const_mul, hnp, hnq]
        norm_num [affinity]
  have hv2 : (∫ ω, v ω ^ 2 ∂ν) = 2 + 2 * affinity p q ν := by
    calc
      _ = ∫ ω, (p ω + q ω) + 2 * (Real.sqrt (p ω) * Real.sqrt (q ω)) ∂ν := by
        apply integral_congr_ae
        filter_upwards [] with ω
        dsimp [v]
        nlinarith [Real.sq_sqrt (hp ω), Real.sq_sqrt (hq ω)]
      _ = _ := by
        rw [integral_add hsum (hprod.const_mul 2), integral_add hip hiq,
          integral_const_mul, hnp, hnq]
        norm_num [affinity]
  have hid : (∫ ω, |p ω - q ω| ∂ν) = ∫ ω, u ω * v ω ∂ν := by
    apply integral_congr_ae
    filter_upwards [] with ω
    dsimp [u, v]
    calc
      |p ω - q ω| = |(Real.sqrt (p ω) - Real.sqrt (q ω)) *
          (Real.sqrt (p ω) + Real.sqrt (q ω))| := by
        congr 1
        nlinarith [Real.sq_sqrt (hp ω), Real.sq_sqrt (hq ω)]
      _ = _ := by
        rw [abs_mul, abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  have hc := cauchy_schwarz_nonneg u v (fun _ => abs_nonneg _)
    (fun _ => add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hu hv
  rw [← hid, hu2, hv2] at hc
  have hA0 := affinity_nonneg (ν := ν) p q
  have hA1 := affinity_le_one p q hp hq hip hiq hnp hnq
  have ha : 0 ≤ 2 - 2 * affinity p q ν := by linarith
  have hb : 0 ≤ 2 + 2 * affinity p q ν := by linarith
  have hab : 0 ≤ 1 - affinity p q ν ^ 2 := by nlinarith
  have hc2 := mul_self_le_mul_self (integral_nonneg (fun ω => abs_nonneg (p ω - q ω))) hc
  have hroota := Real.sq_sqrt ha
  have hrootb := Real.sq_sqrt hb
  have hrootab := Real.sq_sqrt hab
  have hprodroot : (Real.sqrt (2 - 2 * affinity p q ν) *
      Real.sqrt (2 + 2 * affinity p q ν)) ^ 2 = 4 * (1 - affinity p q ν ^ 2) := by
    rw [mul_pow, hroota, hrootb]
    ring
  nlinarith [Real.sqrt_nonneg (1 - affinity p q ν ^ 2)]

/-- Multiplication by a randomized test preserves density integrability. -/
theorem density_mul_test_integrable (p a : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω)
    (hip : Integrable p ν) (ha : AEStronglyMeasurable a ν)
    (ha0 : ∀ ω, 0 ≤ a ω) (ha1 : ∀ ω, a ω ≤ 1) :
    Integrable (fun ω => p ω * a ω) ν := by
  apply hip.mono' (hip.aestronglyMeasurable.mul ha)
  filter_upwards [] with ω
  change ‖p ω * a ω‖ ≤ p ω
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hp ω) (ha0 ω))]
  exact mul_le_of_le_one_right (hp ω) (ha1 ω)

/-- Every measurable randomized test has the stated sum of its two errors.
The test value is its probability of reporting the second hypothesis. -/
theorem randomized_test_error_lower (p q a : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hq : ∀ ω, 0 ≤ q ω)
    (hip : Integrable p ν) (hiq : Integrable q ν)
    (hnp : ∫ ω, p ω ∂ν = 1) (hnq : ∫ ω, q ω ∂ν = 1)
    (ha : AEStronglyMeasurable a ν) (ha0 : ∀ ω, 0 ≤ a ω) (ha1 : ∀ ω, a ω ≤ 1) :
    1 - Real.sqrt (1 - affinity p q ν ^ 2) ≤
      (∫ ω, p ω * a ω ∂ν) + (∫ ω, q ω * (1 - a ω) ∂ν) := by
  have hpa := density_mul_test_integrable p a hp hip ha ha0 ha1
  have hqa := density_mul_test_integrable q (fun ω => 1 - a ω) hq hiq
    (aestronglyMeasurable_const.sub ha)
    (fun ω => sub_nonneg.mpr (ha1 ω))
    (fun ω => by change 1 - a ω ≤ 1; linarith [ha0 ω])
  have habs : Integrable (fun ω => |p ω - q ω|) ν := by
    simpa only [Real.norm_eq_abs] using (hip.sub hiq).norm
  have hsum : Integrable (fun ω => p ω + q ω) ν := hip.add hiq
  have hpoint : ∀ ω, p ω + q ω - |p ω - q ω| ≤
      2 * (p ω * a ω + q ω * (1 - a ω)) := by
    intro ω
    rcases le_total (q ω) (p ω) with hqp | hpq
    · rw [abs_of_nonneg (sub_nonneg.mpr hqp)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hqp) (ha0 ω)]
    · rw [abs_of_nonpos (sub_nonpos.mpr hpq)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hpq) (sub_nonneg.mpr (ha1 ω))]
  have hi := integral_mono_ae ((hip.add hiq).sub habs) ((hpa.add hqa).const_mul 2)
    (Filter.Eventually.of_forall hpoint)
  simp only [Pi.sub_apply, Pi.add_apply] at hi
  rw [integral_sub hsum habs, integral_add hip hiq, integral_const_mul,
    integral_add hpa hqa, hnp, hnq] at hi
  have htv := integral_abs_sub_le p q hp hq hip hiq hnp hnq
  linarith

/-- A squared-affinity bound gives the numerical testing constant used in
the Gaussian two-hypothesis reduction. -/
theorem randomized_test_error_three_quarters (p q a : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hq : ∀ ω, 0 ≤ q ω)
    (hip : Integrable p ν) (hiq : Integrable q ν)
    (hnp : ∫ ω, p ω ∂ν = 1) (hnq : ∫ ω, q ω ∂ν = 1)
    (ha : AEStronglyMeasurable a ν) (ha0 : ∀ ω, 0 ≤ a ω) (ha1 : ∀ ω, a ω ≤ 1)
    (hclose : 15 / 16 ≤ affinity p q ν ^ 2) :
    3 / 4 ≤ (∫ ω, p ω * a ω ∂ν) + (∫ ω, q ω * (1 - a ω) ∂ν) := by
  have h := randomized_test_error_lower p q a hp hq hip hiq hnp hnq ha ha0 ha1
  have hA0 := affinity_nonneg (ν := ν) p q
  have hA1 := affinity_le_one p q hp hq hip hiq hnp hnq
  have hnonneg : 0 ≤ 1 - affinity p q ν ^ 2 := by nlinarith
  have hs := Real.sq_sqrt hnonneg
  nlinarith [Real.sqrt_nonneg (1 - affinity p q ν ^ 2)]

end Bilevel.HellingerTesting
