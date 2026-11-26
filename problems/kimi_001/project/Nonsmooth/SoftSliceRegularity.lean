import Nonsmooth.SoftSliceProperties
import Nonsmooth.PolynomialDensityMoments

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {ι : Type} [Fintype ι]

def SoftSlicePolynomialGrowth (ρ : ℝ) (D : SmoothSliceConstraints ι) : Prop :=
  ∀ t, ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Metric.ball t 1, ∀ x,
    |softSliceScore ρ D r x| ≤ C * (1 + |x| ^ 2) ∧
    |softSliceGamma ρ D r x| ≤ C * (1 + |x| ^ 4)

theorem polynomial_growth_score_derivative (s g : ℝ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hs : ∀ x, |s x| ≤ C * (1 + |x| ^ 2))
    (hg : ∀ x, |g x| ≤ C * (1 + |x| ^ 4)) (x : ℝ) :
    |g x - s x * s x| ≤ (C + 2 * C ^ 2) * (1 + |x| ^ 4) := by
  have hsq := polynomial_growth_square s hC hs x
  norm_num only [show 2 * 2 = 4 from rfl] at hsq
  have hab := abs_sub (g x) (s x * s x)
  rw [← pow_two] at hab
  rw [← pow_two]
  nlinarith [hg x]

def softSliceRegularFamily {ρ : ℝ} (hρ : 1 < ρ) (D : SmoothSliceConstraints ι)
    (hD : ∀ i t x p q, 0 ≤ D.dxx i t x * p ^ 2 + 2 * D.dtx i t x * p * q + D.dtt i t x * q ^ 2)
    (hg : SoftSlicePolynomialGrowth ρ D) : RegularStrongSliceFamily (softSlicePotential ρ D) := by
  have hc := softSlice_data_continuous ρ D
  have ha : 0 < ρ / 2 := by linarith
  have hρ0 : 0 ≤ ρ := by linarith
  have hV := hc.1
  have hs := hc.2.2.1
  have hG := hc.2.2.2.2.2
  have hpair (t : ℝ) : Continuous (fun x : ℝ => (t, x)) := continuous_const.prodMk continuous_id
  have hVx (t : ℝ) : Continuous (softSlicePotential ρ D t) := by
    simpa only [Function.comp_def, Function.uncurry] using hV.comp (hpair t)
  have hsx (t : ℝ) : Continuous (softSliceScore ρ D t) := by
    simpa only [Function.comp_def, Function.uncurry] using hs.comp (hpair t)
  have hGx (t : ℝ) : Continuous (softSliceGamma ρ D t) := by
    simpa only [Function.comp_def, Function.uncurry] using hG.comp (hpair t)
  refine {
    dx := softSliceDx ρ D
    dxx := softSliceDxx ρ D
    score := softSliceScore ρ D
    mixed := softSliceMixed D
    gamma := softSliceGamma ρ D
    measurable := hV.measurable
    dx_continuous := fun t => by
      simpa only [Function.comp_def, Function.uncurry] using
        hc.2.1.comp (hpair t)
    dxx_continuous := fun t => by
      simpa only [Function.comp_def, Function.uncurry] using
        hc.2.2.2.1.comp (hpair t)
    score_continuous := fun t => by
      simpa only [Function.comp_def, Function.uncurry] using
        hs.comp (hpair t)
    mixed_continuous := fun t => by
      simpa only [Function.comp_def, Function.uncurry] using
        hc.2.2.2.2.1.comp (hpair t)
    dx_derivative := softSlicePotential_hasDerivAt_x ρ D
    dxx_derivative := softSliceDx_hasDerivAt_x ρ D
    mixed_derivative := softSliceScore_hasDerivAt_x ρ D
    transverse := fun t x => (softSlice_hessian_bound hρ D hD t x).1
    hessian := fun t x => (softSlice_hessian_bound hρ D hD t x).2
    mean_regular := ?_
    score_regular := ?_
    partition_regular := ?_
    score_memLp := ?_
    gamma_integrable := ?_
  }
  · intro t
    obtain ⟨C, hC, hb⟩ := hg t
    apply potential_polynomial_moment_regular (softSlicePotential ρ D) (softSliceScore ρ D)
      (fun _ (x : ℝ) => x) (fun _ _ => 0) t hV hs continuous_snd continuous_const
      (softSlicePotential_hasDerivAt_t ρ D) (fun r x => hasDerivAt_const r x) ha
      (fun r _ => softSlicePotential_gaussian_lower hρ0 D r)
      (C := 1) (m := 2) (D := 2 * C) (l := 4)
    · intro x
      simp only [one_mul]
      nlinarith [sq_nonneg (|x| - 1)]
    · intro r hr x
      simpa only [zero_sub, abs_neg] using
        polynomial_growth_coordinate_product (softSliceScore ρ D r) hC (fun x => (hb r hr x).1) x
  · intro t
    obtain ⟨C, hC, hb⟩ := hg t
    exact potential_polynomial_moment_regular (softSlicePotential ρ D) (softSliceScore ρ D)
      (softSliceScore ρ D) (softSliceGamma ρ D) t hV hs hs hG
      (softSlicePotential_hasDerivAt_t ρ D) (softSliceScore_hasDerivAt_t ρ D) ha
      (fun r _ => softSlicePotential_gaussian_lower hρ0 D r)
      (fun x => (hb t (by simp) x).1)
      (fun r hr => polynomial_growth_score_derivative _ _ hC
        (fun x => (hb r hr x).1) (fun x => (hb r hr x).2))
  · intro t
    obtain ⟨C, hC, hb⟩ := hg t
    apply potential_polynomial_moment_regular (softSlicePotential ρ D) (softSliceScore ρ D)
      (fun _ _ => 1) (fun _ _ => 0) t hV hs continuous_const continuous_const
      (softSlicePotential_hasDerivAt_t ρ D) (fun r _ => hasDerivAt_const r 1) ha
      (fun r _ => softSlicePotential_gaussian_lower hρ0 D r)
      (C := 1) (m := 0) (D := C) (l := 2)
    · intro x
      norm_num
    · intro r hr x
      simpa only [one_mul, zero_sub, abs_neg] using (hb r hr x).1
  · intro t
    obtain ⟨C, hC, hb⟩ := hg t
    exact real_potential_polynomial_memLp_two (softSlicePotential ρ D t) (softSliceScore ρ D t)
      (hVx t) (hsx t) ha hC
      (softSlicePotential_gaussian_lower hρ0 D t) (fun x => (hb t (by simp) x).1)
  · intro t
    obtain ⟨C, hC, hb⟩ := hg t
    exact real_potential_polynomial_integrable (softSlicePotential ρ D t) (softSliceGamma ρ D t)
      (hVx t) (hGx t) ha
      (softSlicePotential_gaussian_lower hρ0 D t) (fun x => (hb t (by simp) x).2)

theorem softSlice_regular_moment_continuity {ρ : ℝ} (hρ : 1 < ρ) (D : SmoothSliceConstraints ι)
    (hD : ∀ i t x p q, 0 ≤ D.dxx i t x * p ^ 2 + 2 * D.dtx i t x * p * q + D.dtt i t x * q ^ 2)
    (hg : SoftSlicePolynomialGrowth ρ D) :
    RegularSliceMomentContinuity (softSlicePotential ρ D) (softSliceRegularFamily hρ D hD hg) := by
  have hc := softSlice_data_continuous ρ D
  have ha : 0 < ρ / 2 := by linarith
  have hρ0 : 0 ≤ ρ := by linarith
  have hV := hc.1
  have hs := hc.2.2.1
  have hG := hc.2.2.2.2.2
  have hvb (t : ℝ) : ∀ᶠ r in 𝓝 t, ∀ x, ρ / 2 * x ^ 2 ≤ softSlicePotential ρ D r x :=
    Eventually.of_forall (fun r => softSlicePotential_gaussian_lower hρ0 D r)
  constructor
  · intro t
    obtain ⟨C, hC, hb⟩ := hg t
    change PotentialMomentContinuousAt (softSlicePotential ρ D) (softSliceGamma ρ D) t
    apply potential_polynomial_moment_continuous (softSlicePotential ρ D) (softSliceGamma ρ D)
      t hV hG ha (hvb t) (C := C) (m := 4)
    filter_upwards [Metric.ball_mem_nhds t zero_lt_one] with r hr
    exact fun x => (hb r hr x).2
  · intro t
    obtain ⟨C, hC, hb⟩ := hg t
    change PotentialMomentContinuousAt (softSlicePotential ρ D) (fun r x => (softSliceScore ρ D r x) ^ 2) t
    apply potential_polynomial_moment_continuous (softSlicePotential ρ D)
      (fun r x => (softSliceScore ρ D r x) ^ 2) t hV (by convert! hs.pow 2 using 1) ha (hvb t) (C := 2 * C ^ 2) (m := 4)
    filter_upwards [Metric.ball_mem_nhds t zero_lt_one] with r hr
    exact polynomial_growth_square (softSliceScore ρ D r) hC (fun x => (hb r hr x).1)
  · intro t
    obtain ⟨C, hC, hb⟩ := hg t
    change PotentialMomentContinuousAt (softSlicePotential ρ D) (fun r x => x * softSliceScore ρ D r x) t
    apply potential_polynomial_moment_continuous (softSlicePotential ρ D)
      (fun r x => x * softSliceScore ρ D r x) t hV (continuous_snd.mul hs) ha (hvb t) (C := 2 * C) (m := 4)
    filter_upwards [Metric.ball_mem_nhds t zero_lt_one] with r hr
    exact polynomial_growth_coordinate_product (softSliceScore ρ D r) hC (fun x => (hb r hr x).1)

end
end Nonsmooth
