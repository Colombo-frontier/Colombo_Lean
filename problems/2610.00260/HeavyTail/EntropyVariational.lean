import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Entropy variational inequality for actual densities

All expectations are Bochner integrals. `densityMeasure` is the actual measure
obtained by changing density. The Gibbs inequality is proved from the scalar
logarithm inequality and integration; neither KL nonnegativity nor the
variational inequality is assumed. Strictly positive densities cover the
Gaussian-mixture application. Integrability hypotheses are stated explicitly.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace HeavyTail

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}

def densityMeasure (Q : Measure Ω) (w : Ω → ℝ) : Measure Ω :=
  Q.withDensity (fun ω => ENNReal.ofReal (w ω))

def densityRelativeEntropy (Q : Measure Ω) (w v : Ω → ℝ) : ℝ :=
  ∫ ω, w ω * Real.log (w ω / v ω) ∂Q

theorem integral_densityMeasure {w : Ω → ℝ} (hwmeas : Measurable w)
    (hwnonneg : ∀ ω, 0 ≤ w ω) (g : Ω → ℝ) :
    (∫ ω, g ω ∂densityMeasure Q w) = ∫ ω, w ω * g ω ∂Q := by
  rw [densityMeasure, integral_withDensity_eq_integral_toReal_smul
    hwmeas.ennreal_ofReal (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hwnonneg _), smul_eq_mul]

theorem densityMeasure_isProbability {w : Ω → ℝ}
    (hwnonneg : ∀ ω, 0 ≤ w ω) (hwint : Integrable w Q)
    (hwnorm : (∫ ω, w ω ∂Q) = 1) : IsProbabilityMeasure (densityMeasure Q w) := by
  constructor
  rw [densityMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal hwint
      (Filter.Eventually.of_forall hwnonneg), hwnorm]
  norm_num

theorem density_gibbs_pointwise {w v : ℝ} (hw : 0 < w) (hv : 0 < v) :
    w - v ≤ w * Real.log (w / v) := by
  have h := mul_le_mul_of_nonneg_left
    (Real.one_sub_inv_le_log_of_pos (div_pos hw hv)) hw.le
  have heq : w * (1 - (w / v)⁻¹) = w - v := by field_simp
  simpa only [heq] using h

/-- Nonnegativity of the genuine integral KL between two normalized densities. -/
theorem densityRelativeEntropy_nonneg {w v : Ω → ℝ}
    (hwpos : ∀ ω, 0 < w ω) (hvpos : ∀ ω, 0 < v ω)
    (hwint : Integrable w Q) (hvint : Integrable v Q)
    (hentint : Integrable (fun ω => w ω * Real.log (w ω / v ω)) Q)
    (hwnorm : (∫ ω, w ω ∂Q) = 1) (hvnorm : (∫ ω, v ω ∂Q) = 1) :
    0 ≤ densityRelativeEntropy Q w v := by
  have h := integral_mono (hwint.sub hvint) hentint
    (fun ω => density_gibbs_pointwise (hwpos ω) (hvpos ω))
  change (∫ ω, w ω - v ω ∂Q) ≤ (∫ ω, w ω * Real.log (w ω / v ω) ∂Q) at h
  rw [integral_sub hwint hvint, hwnorm, hvnorm, sub_self] at h
  exact h

theorem entropy_exponential_pointwise {w g Z : ℝ} (hw : 0 < w) (hZ : 0 < Z) :
    w * g - w * Real.log w - w * Real.log Z ≤ Real.exp g / Z - w := by
  have hlog := Real.log_le_sub_one_of_pos (div_pos (Real.exp_pos g) (mul_pos hw hZ))
  rw [Real.log_div (Real.exp_ne_zero g) (mul_ne_zero hw.ne' hZ.ne'),
    Real.log_exp, Real.log_mul hw.ne' hZ.ne'] at hlog
  have hm := mul_le_mul_of_nonneg_left hlog hw.le
  have heq : w * (Real.exp g / (w * Z) - 1) = Real.exp g / Z - w := by
    field_simp; ring
  rw [heq] at hm
  nlinarith

/-- Gibbs' variational inequality in weighted-integral form. -/
theorem density_entropy_variational [IsProbabilityMeasure Q] {w g : Ω → ℝ}
    (hwpos : ∀ ω, 0 < w ω) (hwint : Integrable w Q)
    (hwnorm : (∫ ω, w ω ∂Q) = 1)
    (hwgint : Integrable (fun ω => w ω * g ω) Q)
    (hentint : Integrable (fun ω => w ω * Real.log (w ω)) Q)
    (hexpint : Integrable (fun ω => Real.exp (g ω)) Q) :
    (∫ ω, w ω * g ω ∂Q) - (∫ ω, w ω * Real.log (w ω) ∂Q) ≤
      Real.log (∫ ω, Real.exp (g ω) ∂Q) := by
  let Z : ℝ := ∫ ω, Real.exp (g ω) ∂Q
  have hZ : 0 < Z := integral_exp_pos hexpint
  have hleft : Integrable
      (fun ω => w ω * g ω - w ω * Real.log (w ω) - w ω * Real.log Z) Q :=
    (hwgint.sub hentint).sub (hwint.mul_const (Real.log Z))
  have hright : Integrable (fun ω => Real.exp (g ω) / Z - w ω) Q :=
    (hexpint.div_const Z).sub hwint
  have h := integral_mono hleft hright
    (fun ω => entropy_exponential_pointwise (hwpos ω) hZ)
  have hsubint : Integrable (fun ω => w ω * g ω - w ω * Real.log (w ω)) Q :=
    hwgint.sub hentint
  rw [integral_sub hsubint (hwint.mul_const (Real.log Z)),
    integral_sub hwgint hentint, integral_mul_const, hwnorm, one_mul,
    integral_sub (hexpint.div_const Z) hwint, integral_div, hwnorm] at h
  change _ ≤ Z / Z - 1 at h
  rw [div_self hZ.ne', sub_self] at h
  linarith

/-- Exactly `E_P g - E_P log(dP/dQ) ≤ log E_Q exp g`, with `P = Q.withDensity w`. -/
theorem entropy_variational_withDensity [IsProbabilityMeasure Q] {w g : Ω → ℝ}
    (hwmeas : Measurable w) (hwpos : ∀ ω, 0 < w ω) (hwint : Integrable w Q)
    (hwnorm : (∫ ω, w ω ∂Q) = 1)
    (hwgint : Integrable (fun ω => w ω * g ω) Q)
    (hentint : Integrable (fun ω => w ω * Real.log (w ω)) Q)
    (hexpint : Integrable (fun ω => Real.exp (g ω)) Q) :
    (∫ ω, g ω ∂densityMeasure Q w) -
      (∫ ω, Real.log (w ω) ∂densityMeasure Q w) ≤
        Real.log (∫ ω, Real.exp (g ω) ∂Q) := by
  rw [integral_densityMeasure hwmeas (fun ω => (hwpos ω).le),
    integral_densityMeasure hwmeas (fun ω => (hwpos ω).le)]
  exact density_entropy_variational hwpos hwint hwnorm hwgint hentint hexpint

/-- The negative-error version used to upper bound the online stability term. -/
theorem negative_error_entropy_variational [IsProbabilityMeasure Q] {w E : Ω → ℝ}
    (hwmeas : Measurable w) (hwpos : ∀ ω, 0 < w ω) (hwint : Integrable w Q)
    (hwnorm : (∫ ω, w ω ∂Q) = 1)
    (hwEint : Integrable (fun ω => w ω * E ω) Q)
    (hentint : Integrable (fun ω => w ω * Real.log (w ω)) Q)
    (hexpint : Integrable (fun ω => Real.exp (-E ω)) Q) :
    -(∫ ω, E ω ∂densityMeasure Q w) -
      (∫ ω, Real.log (w ω) ∂densityMeasure Q w) ≤
        Real.log (∫ ω, Real.exp (-E ω) ∂Q) := by
  have hneg : Integrable (fun ω => w ω * (-E ω)) Q := by
    simpa only [mul_neg] using hwEint.neg
  have h := entropy_variational_withDensity hwmeas hwpos hwint hwnorm hneg hentint hexpint
  simpa only [integral_neg] using h

end HeavyTail
