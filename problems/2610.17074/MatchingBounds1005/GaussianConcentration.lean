import MatchingBounds1005.GaussianVector
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

import Mathlib.Probability.Distributions.Gaussian
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
# Gaussian square exponential moments

The one-dimensional density computation and product integration below adapt
the existing checked `Nonsmooth/GaussianSquareMGF.lean` proof, with only its
actual Mathlib dependencies. No application-specific assumptions are imported.
The measure is literally the product of independent standard Gaussian laws.
-/

namespace MatchingBounds1005.GaussianConcentration

open MeasureTheory ProbabilityTheory Filter
open scoped Topology
noncomputable section

def gaussianVector (m : ℕ) : Measure (Fin m → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance (m : ℕ) : IsProbabilityMeasure (gaussianVector m) := by
  unfold gaussianVector
  infer_instance

def energy {m : ℕ} (z : Fin m → ℝ) : ℝ := ∑ i, (z i) ^ 2

theorem energy_nonneg {m : ℕ} (z : Fin m → ℝ) : 0 ≤ energy z :=
  Finset.sum_nonneg fun i _ => sq_nonneg (z i)

theorem square_exponential_integral {t : ℝ} (ht : t < 1 / 2) :
    (∫ z : ℝ, Real.exp (t * z ^ 2) ∂gaussianReal 0 1) =
      (Real.sqrt (1 - 2 * t))⁻¹ := by
  have hb : 0 < 1 / 2 - t := by linarith
  have hc : 0 < 1 - 2 * t := by linarith
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
  have he (z : ℝ) : gaussianPDFReal 0 1 z • Real.exp (t * z ^ 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 - t) * z ^ 2) := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul, mul_assoc,
      ← Real.exp_add]
    congr 2
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_gaussian]
  calc
    _ = Real.sqrt (Real.pi / (1 / 2 - t)) / Real.sqrt (2 * Real.pi) := by ring
    _ = Real.sqrt ((Real.pi / (1 / 2 - t)) / (2 * Real.pi)) :=
      (Real.sqrt_div (div_nonneg Real.pi_pos.le hb.le) _).symm
    _ = Real.sqrt ((1 - 2 * t)⁻¹) := by
      congr 1
      field_simp [Real.pi_ne_zero, ne_of_gt hb, ne_of_gt hc]
      ring
    _ = _ := Real.sqrt_inv _

theorem square_exponential_integrable {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun z : ℝ => Real.exp (t * z ^ 2)) (gaussianReal 0 1) := by
  by_contra h
  have hi := square_exponential_integral ht
  rw [integral_undef h] at hi
  have hp : 0 < (Real.sqrt (1 - 2 * t))⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.mpr (by linarith))
  linarith

theorem energy_exponential_integral (m : ℕ) {t : ℝ} (ht : t < 1 / 2) :
    (∫ z, Real.exp (t * energy z) ∂gaussianVector m) =
      ((Real.sqrt (1 - 2 * t))⁻¹) ^ m := by
  have he (z : Fin m → ℝ) : Real.exp (t * energy z) = ∏ i, Real.exp (t * (z i) ^ 2) := by
    rw [energy, Finset.mul_sum, Real.exp_sum]
  simp_rw [he]
  letI : MeasureSpace ℝ := ⟨gaussianReal 0 1⟩
  letI : SigmaFinite (volume : Measure ℝ) := by
    change SigmaFinite (gaussianReal 0 1)
    infer_instance
  have hp := integral_fintype_prod_eq_prod (Fin m) (fun _ (z : ℝ) => Real.exp (t * z ^ 2))
  change (∫ z, ∏ i, Real.exp (t * (z i) ^ 2) ∂gaussianVector m) =
    ∏ _i : Fin m, ∫ z : ℝ, Real.exp (t * z ^ 2) ∂gaussianReal 0 1 at hp
  rw [hp]
  simp only [square_exponential_integral ht, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

theorem energy_exponential_integrable (m : ℕ) {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun z => Real.exp (t * energy z)) (gaussianVector m) := by
  by_contra h
  have hi := energy_exponential_integral m ht
  rw [integral_undef h] at hi
  have hp : 0 < ((Real.sqrt (1 - 2 * t))⁻¹) ^ m := by
    apply pow_pos
    exact inv_pos.mpr (Real.sqrt_pos.mpr (by linarith))
  linarith

theorem energy_exponential_integral_log (m : ℕ) {t : ℝ} (ht : t < 1 / 2) :
    (∫ z, Real.exp (t * energy z) ∂gaussianVector m) =
      Real.exp (-(m : ℝ) / 2 * Real.log (1 - 2 * t)) := by
  rw [energy_exponential_integral m ht]
  have hbase : (Real.sqrt (1 - 2 * t))⁻¹ = Real.exp (-Real.log (1 - 2 * t) / 2) := by
    rw [neg_div, Real.exp_neg, ← Real.log_sqrt (by linarith : 0 ≤ 1 - 2 * t),
      Real.exp_log (Real.sqrt_pos.mpr (by linarith : 0 < 1 - 2 * t))]
  rw [hbase, ← Real.exp_nat_mul]
  congr 1
  ring

/-- The precise logarithmic inequality used for the upper chi-square tail. -/
theorem log_one_add_upper {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.log (1 + u) ≤ u - u ^ 2 / 4 := by
  let f : ℝ → ℝ := fun x => x - Real.log (1 + x) - x ^ 2 / 4
  have hd (x : ℝ) (hx : 0 ≤ x) :
      HasDerivAt f (1 - (1 + x)⁻¹ - (2 * x) / 4) x := by
    convert ((hasDerivAt_id x).sub
      (((hasDerivAt_id x).const_add 1).log (by linarith : 1 + x ≠ 0))).sub
      (((hasDerivAt_id x).pow 2).div_const 4) using 1
    simp [f]
  have hmono : MonotoneOn f (Set.Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · intro x hx
      exact (hd x hx.1).continuousAt.continuousWithinAt
    · intro x hx
      exact (hd x (interior_subset hx).1).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx0 := (interior_subset hx).1
      have hx1 := (interior_subset hx).2
      rw [(hd x hx0).deriv]
      have hp : 0 < 1 + x := by linarith
      have he : 1 - (1+x)⁻¹ - 2*x/4 = x*(1-x)/(2*(1+x)) := by field_simp; ring
      rw [he]
      exact div_nonneg (mul_nonneg hx0 (sub_nonneg.mpr hx1)) (by positivity)
  have h := hmono (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1) ⟨hu, hu1⟩ hu
  dsimp [f] at h
  norm_num at h
  linarith

/-- A lower logarithmic bound valid at every nonnegative argument. -/
theorem log_one_add_lower {u : ℝ} (hu : 0 ≤ u) :
    u - u ^ 2 / 2 ≤ Real.log (1 + u) := by
  have h := Real.le_log_one_add_of_nonneg hu
  apply le_trans _ h
  apply (le_div_iff₀ (by linarith : 0 < u + 2)).2
  nlinarith [pow_nonneg hu 3]

end
end MatchingBounds1005.GaussianConcentration





/-! # Chi-square concentration under the actual product Gaussian law

This proves the first assertion of source `lem:sphere`, including the stated
constant `1/8`, by Gaussian density integration and exponential Markov.
-/

namespace MatchingBounds1005.GaussianConcentration

open MeasureTheory ProbabilityTheory Filter
noncomputable section

theorem exponential_chernoff (m : ℕ) {t : ℝ} (ht : t < 1 / 2) (a : ℝ) :
    (gaussianVector m).real {z | t * a ≤ t * energy z} ≤
      Real.exp (-t * a - (m : ℝ) / 2 * Real.log (1 - 2 * t)) := by
  have hset : {z : Fin m → ℝ | Real.exp (t*a) ≤ Real.exp (t * energy z)} =
      {z | t*a ≤ t * energy z} := by
    ext z
    simp only [Set.mem_setOf_eq, Real.exp_le_exp]
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := gaussianVector m) (f := fun z => Real.exp (t * energy z))
    (ae_of_all _ fun _ => (Real.exp_pos _).le)
    (energy_exponential_integrable m ht) (Real.exp (t*a))
  rw [hset, energy_exponential_integral_log m ht] at hmarkov
  have hbound : (gaussianVector m).real {z | t*a ≤ t*energy z} ≤
      Real.exp (-(m:ℝ)/2*Real.log (1-2*t)) / Real.exp (t*a) :=
    (le_div_iff₀ (Real.exp_pos (t*a))).2 (by simpa only [mul_comm] using hmarkov)
  convert hbound using 1
  rw [← Real.exp_sub]
  congr 1
  ring

theorem chi_square_upper_tail (m : ℕ) {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    (gaussianVector m).real {z | (m : ℝ)*(1+u) ≤ energy z} ≤
      Real.exp (-(m : ℝ) * u ^ 2 / 8) := by
  let t := u / (2*(1+u))
  have hp : 0 < 1+u := by linarith
  have ht0 : 0 < t := div_pos hu (by positivity)
  have ht : t < 1/2 := by
    dsimp [t]
    apply (div_lt_iff₀ (by positivity : 0 < 2*(1+u))).2
    linarith
  have hset : {z : Fin m → ℝ | t*((m:ℝ)*(1+u)) ≤ t*energy z} =
      {z | (m:ℝ)*(1+u) ≤ energy z} := by
    ext z
    exact mul_le_mul_left ht0
  have h := exponential_chernoff m ht ((m:ℝ)*(1+u))
  rw [hset] at h
  have he : 1-2*t = (1+u)⁻¹ := by dsimp [t]; field_simp [ne_of_gt hp]; ring
  rw [he, Real.log_inv] at h
  have hexp : -t*((m:ℝ)*(1+u)) - (m:ℝ)/2*(-Real.log (1+u)) =
      (m:ℝ)/2 * (Real.log (1+u)-u) := by
    dsimp [t]
    field_simp [ne_of_gt hp]
    ring
  rw [hexp] at h
  apply h.trans
  apply Real.exp_le_exp.mpr
  have hlog := log_one_add_upper hu.le hu1
  have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ (m:ℝ)/2)
  nlinarith

theorem chi_square_lower_tail (m : ℕ) {u : ℝ} (hu : 0 < u) :
    (gaussianVector m).real {z | energy z ≤ (m : ℝ)*(1-u)} ≤
      Real.exp (-(m : ℝ) * u ^ 2 / 4) := by
  have ht : -u/2 < (1:ℝ)/2 := by linarith
  have htn : -u/2 < (0:ℝ) := by linarith
  have hset : {z : Fin m → ℝ | (-u/2)*((m:ℝ)*(1-u)) ≤ (-u/2)*energy z} =
      {z | energy z ≤ (m:ℝ)*(1-u)} := by
    ext z
    exact mul_le_mul_left_of_neg htn
  have h := exponential_chernoff m ht ((m:ℝ)*(1-u))
  rw [hset, show 1-2*(-u/2) = 1+u by ring] at h
  apply h.trans
  apply Real.exp_le_exp.mpr
  have hlog := log_one_add_lower hu.le
  have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ (m:ℝ)/2)
  nlinarith

/-- The manuscript's chi-square concentration statement, with all nondegenerate
parameter conditions explicit. The event is defined under a genuine probability
measure, not supplied as a numerical probability parameter. -/
theorem chi_square_two_sided {m : ℕ} (hm : 0 < m) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    (gaussianVector m).real {z | u < |energy z / (m:ℝ) - 1|} ≤
      2 * Real.exp (-(m:ℝ) * u ^ 2 / 8) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  let lower : Set (Fin m → ℝ) := {z | energy z ≤ (m:ℝ)*(1-u)}
  let upper : Set (Fin m → ℝ) := {z | (m:ℝ)*(1+u) ≤ energy z}
  have hsub : {z : Fin m → ℝ | u < |energy z/(m:ℝ)-1|} ⊆ lower ∪ upper := by
    intro z hz
    change u < |energy z/(m:ℝ)-1| at hz
    rcases lt_abs.mp hz with h | h
    · right
      have hd : 1+u < energy z/(m:ℝ) := by linarith
      have := (lt_div_iff₀ hm').mp hd
      dsimp [upper]
      nlinarith
    · left
      have hd : energy z/(m:ℝ) < 1-u := by linarith
      have := (div_lt_iff₀ hm').mp hd
      dsimp [lower]
      nlinarith
  have hlower := chi_square_lower_tail m hu
  have hupper := chi_square_upper_tail m hu hu1.le
  have hlower' : (gaussianVector m).real lower ≤ Real.exp (-(m:ℝ)*u^2/8) := by
    apply hlower.trans
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (Nat.cast_nonneg m : (0:ℝ) ≤ m) (sq_nonneg u)]
  calc
    _ ≤ (gaussianVector m).real (lower ∪ upper) := measureReal_mono hsub
    _ ≤ (gaussianVector m).real lower + (gaussianVector m).real upper := measureReal_union_le _ _
    _ ≤ _ := by linarith

end
end MatchingBounds1005.GaussianConcentration


namespace MatchingBounds1005.GaussianConcentration
open MeasureTheory ProbabilityTheory GaussianVector
noncomputable section

theorem euclidean_energy (m : ℕ) (x : Vec m) :
    energy ((EuclideanSpace.measurableEquiv (Fin m)) x) = ‖x‖ ^ 2 := by
  exact (norm_sq_coordinates x).symm

/-- The actual Euclidean Gaussian norm-square MGF, with its complete
nondegenerate range of parameters. -/
theorem norm_square_exponential_integral (m : ℕ) {t : ℝ} (ht : t < 1 / 2) :
    (∫ x, Real.exp (t * ‖x‖ ^ 2) ∂standardGaussian m) =
      Real.exp (-(m : ℝ) / 2 * Real.log (1 - 2 * t)) := by
  have h := energy_exponential_integral_log m ht
  rw [gaussianVector, ← standardGaussian_coordinate_law m,
    integral_map (EuclideanSpace.measurableEquiv (Fin m)).measurable.aemeasurable
      ((by unfold energy; fun_prop : Continuous
        (fun z : Fin m → ℝ => Real.exp (t * energy z))).measurable.aestronglyMeasurable)] at h
  simpa only [euclidean_energy] using h

/-- The Gaussian radius has exponential two-sided concentration, rather
than a second-moment substitute. -/
theorem norm_square_two_sided {m : ℕ} (hm : 0 < m) {u : ℝ}
    (hu : 0 < u) (hu1 : u < 1) :
    (standardGaussian m).real {x | u < |‖x‖ ^ 2 / (m : ℝ) - 1|} ≤
      2 * Real.exp (-(m : ℝ) * u ^ 2 / 8) := by
  have hs : MeasurableSet {z : Fin m → ℝ | u < |energy z / (m : ℝ) - 1|} := by
    apply measurableSet_lt measurable_const
    unfold energy
    fun_prop
  have h := chi_square_two_sided hm hu hu1
  rw [gaussianVector, ← standardGaussian_coordinate_law m,
    map_measureReal_apply (EuclideanSpace.measurableEquiv (Fin m)).measurable hs] at h
  simpa only [Set.preimage_setOf_eq, euclidean_energy] using h

end
end MatchingBounds1005.GaussianConcentration

