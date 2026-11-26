import Mathlib
import SLT.GaussianMeasure

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Task006.GaussianRadius

lemma gaussian_second_moment :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1 := by
  have h := variance_eq_sub (memLp_id_gaussianReal (μ := 0) (v := 1) 2)
  simpa [Pi.pow_apply] using h.symm

lemma gaussian_fourth_moment :
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) = 3 := by
  let f : ℝ → ℝ := fun t => Real.exp (t ^ 2 / 2)
  have he (t : ℝ) : HasDerivAt f (t * f t) t := by
    convert (Real.hasDerivAt_exp (t ^ 2 / 2)).comp t
      (((hasDerivAt_id t).pow 2).div_const 2) using 1 <;> first | rfl | (simp only [f, id_eq]; ring)
  have h1 : deriv f = fun t => t * f t := funext (fun t => (he t).deriv)
  have h2 : deriv (fun t => t * f t) = fun t => (1 + t ^ 2) * f t := by
    funext t
    convert ((hasDerivAt_id t).mul (he t)).deriv using 1 <;> first | rfl | (simp only [id_eq]; ring)
  have h3 : deriv (fun t => (1 + t ^ 2) * f t) = fun t => (3 * t + t ^ 3) * f t := by
    funext t
    convert (((hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).pow 2)).mul
      (he t)).deriv using 1 <;> first | rfl | (simp only [id_eq, Pi.add_apply, Pi.pow_apply]; ring)
  have h4 : deriv (fun t => (3 * t + t ^ 3) * f t) =
      fun t => (3 + 6 * t ^ 2 + t ^ 4) * f t := by
    funext t
    convert ((((hasDerivAt_const t (3 : ℝ)).mul (hasDerivAt_id t)).add
      ((hasDerivAt_id t).pow 3)).mul (he t)).deriv using 1 <;> first | rfl | (simp only [id_eq, Pi.mul_apply, Pi.add_apply, Pi.pow_apply]; ring)
  have hm : mgf (fun x : ℝ => x) (gaussianReal 0 1) = f := by
    funext t
    simp [mgf_fun_id_gaussianReal, f]
  have hmom := iteratedDeriv_mgf_zero
    (X := fun x : ℝ => x) (μ := gaussianReal 0 1) (by simp) 4
  rw [hm] at hmom
  have hd : iteratedDeriv 4 f 0 = 3 := by
    norm_num [iteratedDeriv_succ, iteratedDeriv_zero, h1, h2, h3, h4, f]
  simpa only [Pi.pow_apply, hd] using hmom.symm

lemma gaussian_power_integrable (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 1) := by
  apply integrable_pow_of_integrable_exp_mul (t := 1) one_ne_zero
  · simpa using integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (1 : ℝ)
  · simpa using integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-1 : ℝ)

lemma coordinate_power_integrable (n : ℕ) (i : Fin n) (k : ℕ) :
    Integrable (fun w : Fin n → ℝ => w i ^ k) (GaussianMeasure.stdGaussianPi n) := by
  have hm := GaussianMeasure.map_eval_stdGaussianPi i
  have hI : Integrable (fun x : ℝ => x ^ k)
      ((GaussianMeasure.stdGaussianPi n).map (fun w => w i)) := by
    rw [hm]
    exact gaussian_power_integrable k
  exact (integrable_map_measure ((continuous_id.pow k).measurable.aestronglyMeasurable)
    (measurable_pi_apply i).aemeasurable).mp hI

lemma coordinate_second_moment (n : ℕ) (i : Fin n) :
    (∫ w : Fin n → ℝ, w i ^ 2 ∂GaussianMeasure.stdGaussianPi n) = 1 := by
  rw [← gaussian_second_moment, ← GaussianMeasure.map_eval_stdGaussianPi i,
    integral_map (measurable_pi_apply i).aemeasurable (by fun_prop)]

lemma coordinate_fourth_moment (n : ℕ) (i : Fin n) :
    (∫ w : Fin n → ℝ, w i ^ 4 ∂GaussianMeasure.stdGaussianPi n) = 3 := by
  rw [← gaussian_fourth_moment, ← GaussianMeasure.map_eval_stdGaussianPi i,
    integral_map (measurable_pi_apply i).aemeasurable (by fun_prop)]

noncomputable def squaredRadius {n : ℕ} (w : Fin n → ℝ) : ℝ := ∑ i, w i ^ 2

lemma squaredRadius_integrable (n : ℕ) :
    Integrable (squaredRadius (n := n)) (GaussianMeasure.stdGaussianPi n) := by
  exact integrable_finsetSum Finset.univ (fun i _ => coordinate_power_integrable n i 2)

lemma squaredRadius_mean (n : ℕ) :
    (∫ w, squaredRadius w ∂GaussianMeasure.stdGaussianPi n) = (n : ℝ) := by
  change (∫ w : Fin n → ℝ, ∑ i, w i ^ 2 ∂GaussianMeasure.stdGaussianPi n) = (n : ℝ)
  rw [integral_finsetSum Finset.univ
    (fun i _ => coordinate_power_integrable n i 2)]
  simp [coordinate_second_moment]



lemma squaredRadius_sq_bound (n : ℕ) (w : Fin n → ℝ) :
    squaredRadius w ^ 2 ≤ (n : ℝ) * ∑ i, w i ^ 4 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : Fin n => w i ^ 2) (fun _ => (1 : ℝ))
  simpa [squaredRadius, ← pow_mul, mul_comm] using h

lemma squaredRadius_sq_integrable (n : ℕ) :
    Integrable (fun w : Fin n → ℝ => squaredRadius w ^ 2)
      (GaussianMeasure.stdGaussianPi n) := by
  have hdom := (integrable_finsetSum Finset.univ
    (fun i _ => coordinate_power_integrable n i 4)).const_mul (n : ℝ)
  have hcont : Continuous (fun w : Fin n → ℝ => squaredRadius w ^ 2) := by
    unfold squaredRadius
    exact (continuous_finsetSum Finset.univ (fun i _ => (continuous_apply i).pow 2)).pow 2
  apply hdom.mono' hcont.aestronglyMeasurable
  filter_upwards with w
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (squaredRadius w))]
  exact squaredRadius_sq_bound n w

lemma squaredRadius_fourth_bound (n : ℕ) :
    (∫ w : Fin n → ℝ, squaredRadius w ^ 2 ∂GaussianMeasure.stdGaussianPi n) ≤
      3 * (n : ℝ) ^ 2 := by
  calc
    (∫ w : Fin n → ℝ, squaredRadius w ^ 2 ∂GaussianMeasure.stdGaussianPi n)
        ≤ ∫ w : Fin n → ℝ, (n : ℝ) * ∑ i, w i ^ 4
          ∂GaussianMeasure.stdGaussianPi n :=
      integral_mono (squaredRadius_sq_integrable n)
        ((integrable_finsetSum Finset.univ
          (fun i _ => coordinate_power_integrable n i 4)).const_mul (n : ℝ))
        (squaredRadius_sq_bound n)
    _ = 3 * (n : ℝ) ^ 2 := by
      rw [integral_const_mul, integral_finsetSum Finset.univ
        (fun i _ => coordinate_power_integrable n i 4)]
      simp [coordinate_fourth_moment]
      ring

/-- A proved small-ball estimate from first and second moments. -/
theorem paley_half_of_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (a : ℝ)
    (ha : 0 < a) (hX : Measurable X) (hnonneg : ∀ ω, 0 ≤ X ω)
    (hI : Integrable X μ) (hI2 : Integrable (fun ω => X ω ^ 2) μ)
    (hmean : (∫ ω, X ω ∂μ) = a)
    (hsecond : (∫ ω, X ω ^ 2 ∂μ) ≤ 3 * a ^ 2) :
    (1 / 12 : ℝ) ≤ μ.real {ω | a / 2 ≤ X ω} := by
  let E := {ω | a / 2 ≤ X ω}
  have hE : MeasurableSet E := measurableSet_le measurable_const hX
  have hIE : Integrable (E.indicator X) μ := hI.indicator hE
  have hpoint : ∀ ω, X ω ≤ a / 2 + E.indicator X ω := by
    intro ω
    by_cases h : ω ∈ E
    · simp only [Set.indicator_of_mem h]; linarith
    · have hx : X ω < a / 2 := lt_of_not_ge h
      simp only [Set.indicator_of_notMem h]
      simpa only [add_zero] using hx.le
  have hhalf : a / 2 ≤ ∫ ω, E.indicator X ω ∂μ := by
    have h := integral_mono hI ((integrable_const (a / 2)).add hIE) hpoint
    change (∫ ω, X ω ∂μ) ≤ ∫ ω, a / 2 + E.indicator X ω ∂μ at h
    rw [integral_add (integrable_const _) hIE] at h
    have hc : (∫ _ω : Ω, a / 2 ∂μ) = a / 2 := by simp
    rw [hmean, hc] at h
    linarith
  have hLpX : MemLp X 2 μ := (memLp_two_iff_integrable_sq hX.aestronglyMeasurable).mpr hI2
  have hLpOne : MemLp (E.indicator (fun _ : Ω => (1 : ℝ))) 2 μ :=
    (memLp_const (1 : ℝ)).indicator hE
  have hHolder : (2 : ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have hOne_nonneg : ∀ ω, 0 ≤ E.indicator (fun _ : Ω => (1 : ℝ)) ω := by
    intro ω
    by_cases h : ω ∈ E <;> simp [h]
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg hHolder
    (ae_of_all μ hnonneg) (ae_of_all μ hOne_nonneg)
    (by convert hLpX using 1 <;> norm_num)
    (by convert hLpOne using 1 <;> norm_num)
  have hleft : (∫ ω, X ω * E.indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ) =
      ∫ ω, E.indicator X ω ∂μ := by
    apply integral_congr_ae
    filter_upwards with ω
    by_cases h : ω ∈ E <;> simp [h]
  have hright : (∫ ω, (E.indicator (fun _ : Ω => (1 : ℝ)) ω) ^ (2 : ℝ) ∂μ) =
      μ.real E := by
    have hp : (fun ω => (E.indicator (fun _ : Ω => (1 : ℝ)) ω) ^ (2 : ℝ)) =
        E.indicator (fun _ : Ω => (1 : ℝ)) := by
      funext ω
      by_cases h : ω ∈ E <;> simp [h]
    rw [hp, integral_indicator hE]
    simp
  rw [hleft, hright] at hCS
  have hs : (∫ ω, E.indicator X ω ∂μ) ^ 2 ≤
      (∫ ω, X ω ^ 2 ∂μ) * μ.real E := by
    have hn : 0 ≤ ∫ ω, E.indicator X ω ∂μ := by linarith [hhalf]
    have hCS' : (∫ ω, E.indicator X ω ∂μ) ≤
        Real.sqrt (∫ ω, X ω ^ 2 ∂μ) * Real.sqrt (μ.real E) := by
      simpa only [Real.sqrt_eq_rpow, Real.rpow_two] using hCS
    have hpow := pow_le_pow_left₀ hn hCS' 2
    have hnI : 0 ≤ ∫ ω, X ω ^ 2 ∂μ := integral_nonneg (fun ω => sq_nonneg _)
    have hnP : 0 ≤ μ.real E := ENNReal.toReal_nonneg
    simpa only [mul_pow, Real.sq_sqrt hnI, Real.sq_sqrt hnP] using hpow
  have hlow := pow_le_pow_left₀ (by linarith : 0 ≤ a / 2) hhalf 2
  have hupper := mul_le_mul_of_nonneg_right hsecond (show 0 ≤ μ.real E from ENNReal.toReal_nonneg)
  have hscaled : a ^ 2 * (1 / 12 : ℝ) ≤ a ^ 2 * μ.real E := by
    nlinarith [hlow, hs, hupper]
  exact le_of_mul_le_mul_of_pos_left hscaled (sq_pos_of_pos ha)



/-- A dimension-independent amount of Gaussian mass lies outside half the
usual radius. This is proved from actual Gaussian moments, not assumed. -/
theorem gaussian_annulus_probability (n : ℕ) (hn : 0 < n) :
    (1 / 12 : ℝ) ≤ (GaussianMeasure.stdGaussianE n).real
      {x | Real.sqrt (n : ℝ) / 2 ≤ ‖x‖} := by
  have hm : Measurable (squaredRadius (n := n)) := by
    unfold squaredRadius
    exact (continuous_finsetSum Finset.univ
      (fun i _ => (continuous_apply i).pow 2)).measurable
  have hnonneg : ∀ w : Fin n → ℝ, 0 ≤ squaredRadius w := by
    intro w
    exact Finset.sum_nonneg (fun i _ => sq_nonneg (w i))
  have hP := paley_half_of_moments (GaussianMeasure.stdGaussianPi n)
    squaredRadius (n : ℝ) (by exact_mod_cast hn) hm hnonneg
    (squaredRadius_integrable n) (squaredRadius_sq_integrable n)
    (squaredRadius_mean n) (squaredRadius_fourth_bound n)
  let e := (EuclideanSpace.equiv (Fin n) ℝ).symm
  have hE : MeasurableSet {x : EuclideanSpace ℝ (Fin n) |
      Real.sqrt (n : ℝ) / 2 ≤ ‖x‖} := measurableSet_le measurable_const (by fun_prop)
  change (1 / 12 : ℝ) ≤
    ((Measure.map e (GaussianMeasure.stdGaussianPi n))
      {x | Real.sqrt (n : ℝ) / 2 ≤ ‖x‖}).toReal
  rw [Measure.map_apply e.continuous.measurable hE]
  apply hP.trans
  apply ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
  intro w hw
  change Real.sqrt (n : ℝ) / 2 ≤ ‖e w‖
  have hs : ‖e w‖ ^ 2 = squaredRadius w := by
    rw [EuclideanSpace.real_norm_sq_eq]
    unfold squaredRadius
    apply Finset.sum_congr rfl
    intro i _
    congr 1
  have hsqrt := Real.sq_sqrt (show 0 ≤ (n : ℝ) from Nat.cast_nonneg _)
  have hnorm := norm_nonneg (e w)
  have hsr := Real.sqrt_nonneg (n : ℝ)
  change (n : ℝ) / 2 ≤ squaredRadius w at hw
  nlinarith

end Task006.GaussianRadius
