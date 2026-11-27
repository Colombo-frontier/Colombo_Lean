import Nonsmooth.OffsetGaussianMomentRegularity
import Nonsmooth.SoftSliceRegularity
import Nonsmooth.ParameterizedMarginalCurvature
import Nonsmooth.PolynomialVectorDensityMoments

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {ι : Type}

def smoothSliceDataPolynomialGrowth (D : SmoothSliceConstraints ι) (i : ι) : Prop :=
  ∀ t, ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Metric.ball t 1, ∀ x,
    |D.dt i r x| ≤ C * (1 + |x| ^ 2) ∧ |D.dtt i r x| ≤ C * (1 + |x| ^ 4)

def regularStrongSliceFamilyOfSmoothData (D : SmoothSliceConstraints ι) (i : ι)
    {ρ a B : ℝ} (hρ : 1 < ρ) (ha : 0 < a)
    (hblock : ∀ t x p q, ρ * (p ^ 2 + q ^ 2) ≤
      D.dxx i t x * p ^ 2 + 2 * D.dtx i t x * p * q + D.dtt i t x * q ^ 2)
    (hVb : ∀ t x, a * x ^ 2 - B ≤ D.value i t x)
    (hg : smoothSliceDataPolynomialGrowth D i) : RegularStrongSliceFamily (D.value i) := by
  have hp (t : ℝ) : Continuous (fun x : ℝ => (t, x)) := continuous_const.prodMk continuous_id
  refine {
    dx := D.dx i
    dxx := D.dxx i
    score := D.dt i
    mixed := D.dtx i
    gamma := D.dtt i
    measurable := (D.value_cont i).measurable
    dx_continuous := fun t => (D.dx_cont i).comp (hp t)
    dxx_continuous := fun t => (D.dxx_cont i).comp (hp t)
    score_continuous := fun t => (D.dt_cont i).comp (hp t)
    mixed_continuous := fun t => (D.dtx_cont i).comp (hp t)
    dx_derivative := D.value_dx i
    dxx_derivative := D.dx_dx i
    mixed_derivative := D.dt_dx i
    transverse := fun t x => (hessian_determinant_with_margin hρ (hblock t x)).1
    hessian := fun t x => (hessian_determinant_with_margin hρ (hblock t x)).2
    mean_regular := ?_
    score_regular := ?_
    partition_regular := ?_
    score_memLp := ?_
    gamma_integrable := ?_
  }
  · intro t
    obtain ⟨C, hC, hb⟩ := hg t
    apply potential_offset_moment_regular (D.value i) (D.dt i) (fun _ (x : ℝ) => x) (fun _ _ => 0)
      t (D.value_cont i) (D.dt_cont i) continuous_snd continuous_const
      (D.value_dt i) (fun r x => hasDerivAt_const r x) ha (fun r _ => hVb r)
      (C := 1) (m := 2) (D := 2 * C) (l := 4)
    · intro x
      simp only [one_mul]
      nlinarith [sq_nonneg (|x| - 1)]
    · intro r hr x
      simpa only [zero_sub, abs_neg] using polynomial_growth_coordinate_product
        (D.dt i r) hC (fun x => (hb r hr x).1) x
  · intro t
    obtain ⟨C, hC, hb⟩ := hg t
    exact potential_offset_moment_regular (D.value i) (D.dt i) (D.dt i) (D.dtt i)
      t (D.value_cont i) (D.dt_cont i) (D.dt_cont i) (D.dtt_cont i)
      (D.value_dt i) (D.dt_dt i) ha (fun r _ => hVb r)
      (fun x => (hb t (by simp) x).1)
      (fun r hr => polynomial_growth_score_derivative _ _ hC
        (fun x => (hb r hr x).1) (fun x => (hb r hr x).2))
  · intro t
    obtain ⟨C, hC, hb⟩ := hg t
    apply potential_offset_moment_regular (D.value i) (D.dt i) (fun _ _ => 1) (fun _ _ => 0)
      t (D.value_cont i) (D.dt_cont i) continuous_const continuous_const
      (D.value_dt i) (fun r _ => hasDerivAt_const r 1) ha (fun r _ => hVb r)
      (C := 1) (m := 0) (D := C) (l := 2)
    · intro x
      norm_num
    · intro r hr x
      simpa only [one_mul, zero_sub, abs_neg] using (hb r hr x).1
  · intro t
    obtain ⟨C, hC, hb⟩ := hg t
    apply potential_vector_polynomial_memLp_two (D.value i t) (D.dt i t)
      ((D.value_cont i).comp (hp t)) ((D.dt_cont i).comp (hp t)) ha hC (hVb t)
    intro x
    simpa only [Real.norm_eq_abs] using (hb t (by simp) x).1
  · intro t
    obtain ⟨C, hC, hb⟩ := hg t
    apply potential_vector_polynomial_integrable (D.value i t) (D.dtt i t)
      ((D.value_cont i).comp (hp t)) ((D.dtt_cont i).comp (hp t)) ha (hVb t)
    intro x
    simpa only [Real.norm_eq_abs] using (hb t (by simp) x).2

theorem smoothSliceData_regular_moment_continuity (D : SmoothSliceConstraints ι) (i : ι)
    {ρ a B : ℝ} (hρ : 1 < ρ) (ha : 0 < a)
    (hblock : ∀ t x p q, ρ * (p ^ 2 + q ^ 2) ≤
      D.dxx i t x * p ^ 2 + 2 * D.dtx i t x * p * q + D.dtt i t x * q ^ 2)
    (hVb : ∀ t x, a * x ^ 2 - B ≤ D.value i t x)
    (hg : smoothSliceDataPolynomialGrowth D i) :
    RegularSliceMomentContinuity (D.value i)
      (regularStrongSliceFamilyOfSmoothData D i hρ ha hblock hVb hg) := by
  have hvb (t : ℝ) : ∀ᶠ r in 𝓝 t, ∀ x, a * x ^ 2 - B ≤ D.value i r x :=
    Eventually.of_forall hVb
  constructor
  · intro t
    obtain ⟨C, hC, hb⟩ := hg t
    change PotentialMomentContinuousAt (D.value i) (D.dtt i) t
    apply potential_offset_moment_continuous (D.value i) (D.dtt i) t
      (D.value_cont i) (D.dtt_cont i) ha (hvb t) (C := C) (m := 4)
    filter_upwards [Metric.ball_mem_nhds t zero_lt_one] with r hr
    exact fun x => (hb r hr x).2
  · intro t
    obtain ⟨C, hC, hb⟩ := hg t
    change PotentialMomentContinuousAt (D.value i) (fun r x => (D.dt i r x) ^ 2) t
    apply potential_offset_moment_continuous (D.value i) (fun r x => (D.dt i r x) ^ 2) t
      (D.value_cont i)
      (by convert! (D.dt_cont i).pow 2 using 1)
      ha (hvb t) (C := 2 * C ^ 2) (m := 4)
    filter_upwards [Metric.ball_mem_nhds t zero_lt_one] with r hr
    exact polynomial_growth_square (D.dt i r) hC (fun x => (hb r hr x).1)
  · intro t
    obtain ⟨C, hC, hb⟩ := hg t
    change PotentialMomentContinuousAt (D.value i) (fun r x => x * D.dt i r x) t
    apply potential_offset_moment_continuous (D.value i) (fun r x => x * D.dt i r x) t
      (D.value_cont i) (continuous_snd.mul (D.dt_cont i)) ha (hvb t) (C := 2 * C) (m := 4)
    filter_upwards [Metric.ball_mem_nhds t zero_lt_one] with r hr
    exact polynomial_growth_coordinate_product (D.dt i r) hC (fun x => (hb r hr x).1)

theorem smoothSliceData_regular_exists (D : SmoothSliceConstraints ι) (i : ι)
    {ρ a B : ℝ} (hρ : 1 < ρ) (ha : 0 < a)
    (hblock : ∀ t x p q, ρ * (p ^ 2 + q ^ 2) ≤
      D.dxx i t x * p ^ 2 + 2 * D.dtx i t x * p * q + D.dtt i t x * q ^ 2)
    (hVb : ∀ t x, a * x ^ 2 - B ≤ D.value i t x)
    (hg : smoothSliceDataPolynomialGrowth D i) :
    ∃ H : RegularStrongSliceFamily (D.value i), RegularSliceMomentContinuity (D.value i) H :=
  ⟨regularStrongSliceFamilyOfSmoothData D i hρ ha hblock hVb hg,
    smoothSliceData_regular_moment_continuity D i hρ ha hblock hVb hg⟩

end
end Nonsmooth
