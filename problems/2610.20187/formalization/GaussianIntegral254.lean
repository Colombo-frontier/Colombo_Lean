import GaussianAnalysis254
import Mathlib.Probability.Distributions.Gaussian.Real

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Paper254

theorem gaussian_quadratic_exponent (a v lam x : ℝ) (hv : v ≠ 0)
    (hden : 1+2*lam^2*v ≠ 0) :
    -(x-a)^2/(2*v)-lam*x-lam^2*x^2 =
      (-lam*a-lam^2*a^2+lam^2*v/2)/(1+2*lam^2*v)-
        (x-(a-lam*v)/(1+2*lam^2*v))^2/(2*(v/(1+2*lam^2*v))) := by
  generalize he : 1+2*lam^2*v = D at *
  field_simp [hv,hden]
  rw [← he]
  ring

theorem gaussian_quadratic_integral_pos (a lam : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    (∫ x, Real.exp (-lam*x-lam^2*x^2) ∂gaussianReal a v) =
      (Real.sqrt (1+2*lam^2*(v:ℝ)))⁻¹ *
        Real.exp ((-lam*a-lam^2*a^2+lam^2*(v:ℝ)/2)/(1+2*lam^2*(v:ℝ))) := by
  have hvp : (0:ℝ)<v := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  let D := 1+2*lam^2*(v:ℝ)
  have hD : 0<D := by dsimp [D]; positivity
  let w : ℝ≥0 := ⟨(v:ℝ)/D,by positivity⟩
  have hwp : (0:ℝ)<w := div_pos hvp hD
  have hw : w ≠ 0 := by exact_mod_cast hwp.ne'
  let m := (a-lam*v)/D
  let K := (-lam*a-lam^2*a^2+lam^2*(v:ℝ)/2)/D
  have hroot : Real.sqrt (2*Real.pi*(w:ℝ))*Real.sqrt D=Real.sqrt (2*Real.pi*(v:ℝ)) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    dsimp [w]
    field_simp
  have hpref : (Real.sqrt (2*Real.pi*(v:ℝ)))⁻¹ =
      (Real.sqrt D)⁻¹*(Real.sqrt (2*Real.pi*(w:ℝ)))⁻¹ := by rw [← hroot,mul_inv_rev]
  have hid : ∀ x,gaussianPDFReal a v x * Real.exp (-lam*x-lam^2*x^2)=
      ((Real.sqrt D)⁻¹*Real.exp K)*gaussianPDFReal m w x := by
    intro x
    rw [gaussianPDFReal_def,gaussianPDFReal_def]
    have he := gaussian_quadratic_exponent a v lam x hvp.ne' hD.ne'
    change -(x-a)^2/(2*(v:ℝ))-lam*x-lam^2*x^2=K-(x-m)^2/(2*(w:ℝ)) at he
    rw [hpref]
    calc
      _ = (Real.sqrt D)⁻¹*(Real.sqrt (2*Real.pi*(w:ℝ)))⁻¹*
          Real.exp (-(x-a)^2/(2*(v:ℝ))-lam*x-lam^2*x^2) := by rw [show -(x-a)^2/(2*(v:ℝ))-lam*x-lam^2*x^2= -(x-a)^2/(2*(v:ℝ))+(-lam*x-lam^2*x^2) by ring,Real.exp_add]; ring
      _ = _ := by rw [he,sub_eq_add_neg,Real.exp_add]; simp only [neg_div]; ring
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  simp_rw [hid]
  rw [integral_const_mul,integral_gaussianPDFReal_eq_one _ hw,mul_one]

theorem gaussian_quadratic_integral (a lam : ℝ) (v : ℝ≥0) :
    (∫ x, Real.exp (-lam*x-lam^2*x^2) ∂gaussianReal a v) =
      (Real.sqrt (1+2*lam^2*(v:ℝ)))⁻¹ *
        Real.exp ((-lam*a-lam^2*a^2+lam^2*(v:ℝ)/2)/(1+2*lam^2*(v:ℝ))) := by
  by_cases hv : v=0
  · subst v
    simp [gaussianReal_zero_var]
  · exact gaussian_quadratic_integral_pos a lam v hv

theorem gaussian_log_mixgap_identity (a lam : ℝ) (v : ℝ≥0) :
    Real.log ((∫ x,Real.exp (-lam*x-lam^2*x^2) ∂gaussianReal a v)/
      Real.exp (-lam*a-lam^2*a^2)) =
    -Real.log (1+2*lam^2*(v:ℝ))/2+
      (2*lam^2*(v:ℝ))*(1+2*lam*a)^2/(4*(1+2*lam^2*(v:ℝ))) := by
  have hD : 0<1+2*lam^2*(v:ℝ) := by positivity
  have hs : 0<Real.sqrt (1+2*lam^2*(v:ℝ)) := Real.sqrt_pos.mpr hD
  rw [gaussian_quadratic_integral,Real.log_div (by positivity) (Real.exp_ne_zero _),
    Real.log_mul (inv_ne_zero hs.ne') (Real.exp_ne_zero _),Real.log_inv,
    Real.log_sqrt hD.le,Real.log_exp,Real.log_exp]
  field_simp
  <;> ring

/-- The manuscript's Gaussian mixability gap as an actual probability
integral, including the degenerate variance case. -/
theorem gaussian_integral_mixgap (a lam : ℝ) (v : ℝ≥0) (ha : |2*lam*a|≤1/4) :
    (∫ x,Real.exp (-lam*x-lam^2*x^2) ∂gaussianReal a v) ≤ Real.exp (-lam*a-lam^2*a^2) := by
  have hid := gaussian_log_mixgap_identity a lam v
  have hg := gaussian_gap_formula_nonpos (2*lam^2*(v:ℝ)) (2*lam*a) (by positivity) ha
  have hi : 0 < ∫ x,Real.exp (-lam*x-lam^2*x^2) ∂gaussianReal a v := by
    rw [gaussian_quadratic_integral]
    positivity
  have he := Real.exp_pos (-lam*a-lam^2*a^2)
  have hr : 0 < (∫ x,Real.exp (-lam*x-lam^2*x^2) ∂gaussianReal a v)/Real.exp (-lam*a-lam^2*a^2) := div_pos hi he
  have hlog : Real.log ((∫ x,Real.exp (-lam*x-lam^2*x^2) ∂gaussianReal a v)/Real.exp (-lam*a-lam^2*a^2))≤0 := by linarith
  have hb := (Real.log_nonpos_iff hr.le).mp hlog
  exact (div_le_one he).mp hb

end Paper254
#print axioms Paper254.gaussian_integral_mixgap
