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

namespace GradientHessian.GaussianSquare

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
end GradientHessian.GaussianSquare
