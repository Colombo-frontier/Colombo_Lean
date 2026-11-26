import Bilevel.PolishedLiteralProfiles
import Bilevel.ChiBoundedChainSquareRoot

noncomputable section
namespace Bilevel.PolishedLiteral
open ZeroChainGate

def psiRoot (t : ℝ) : ℝ :=
  Real.exp (1/2) * gate (Real.sqrt 2*(2*t-1))

theorem psiRoot_nonneg (t : ℝ) : 0≤psiRoot t :=
  mul_nonneg (Real.exp_pos _).le (gate_nonneg _)

theorem psiRoot_sq (t : ℝ) : (psiRoot t)^2=psi t := by
  have hs : 0<Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  by_cases ht : t≤1/2
  · rw [psiRoot,gate_zero (mul_nonpos_of_nonneg_of_nonpos hs.le (by linarith)),mul_zero,zero_pow (by omega),psi_zero ht]
  · have hx : 0<2*t-1 := by linarith
    rw [psiRoot,gate_pos_formula (mul_pos hs hx),psi_source_formula,if_neg ht,mul_pow,
      ← Real.exp_nat_mul,← Real.exp_nat_mul,← Real.exp_add]
    congr 1
    have he : (2:ℝ)*(1/2)+2*(-((Real.sqrt 2*(2*t-1))⁻¹)^2)=1-((2*t-1)⁻¹)^2 := by
      field_simp
      nlinarith [hs2]
    exact he

theorem psiRoot_contDiff {k : ℕ∞} : ContDiff ℝ k psiRoot :=
  contDiff_const.mul (gate_contDiff.comp
    (contDiff_const.mul ((contDiff_const.mul contDiff_id).sub contDiff_const)))

theorem psiRoot_hasDerivAt (t : ℝ) : HasDerivAt psiRoot
    (Real.exp (1/2)*(2*Real.sqrt 2)*deriv gate (Real.sqrt 2*(2*t-1))) t := by
  have ha : HasDerivAt (fun s : ℝ => Real.sqrt 2*(2*s-1)) (2*Real.sqrt 2) t := by
    convert ((((hasDerivAt_id t).const_mul 2).sub_const 1).const_mul (Real.sqrt 2)) using 1
    ring
  have h := (((gate_contDiff (n:=1)).differentiable (by norm_num) _).hasDerivAt.comp t ha).const_mul
    (Real.exp (1/2))
  convert h using 1
  ring

theorem psiRoot_derivative_bounded : ∃ B : ℝ,0≤B ∧ ∀ t,|deriv psiRoot t|≤B := by
  obtain ⟨K,hK,hb⟩ := gate_derivative_bounded 1
  refine ⟨Real.exp (1/2)*(2*Real.sqrt 2)*K,by positivity,fun t => ?_⟩
  rw [(psiRoot_hasDerivAt t).deriv,abs_mul,
    abs_of_nonneg (by positivity : 0≤Real.exp (1/2)*(2*Real.sqrt 2))]
  exact mul_le_mul_of_nonneg_left (by simpa only [iteratedDeriv_one] using hb _) (by positivity)

theorem psi_sqrt_derivative : ∃ C : ℝ,0≤C ∧ ∀ t,|deriv psi t|≤C*Real.sqrt (psi t) := by
  obtain ⟨B,hB,hb⟩ := psiRoot_derivative_bounded
  refine ⟨2*B,by positivity,fun t => ?_⟩
  have h := ((psiRoot_contDiff (k:=1)).differentiable (by norm_num) t).hasDerivAt.pow 2
  have he : (fun s : ℝ => (psiRoot s)^2)=psi := funext psiRoot_sq
  rw [he] at h
  norm_num only at h
  simp only [pow_one] at h
  have hs : Real.sqrt (psi t)=psiRoot t := by
    rw [← psiRoot_sq t,Real.sqrt_sq_eq_abs,abs_of_nonneg (psiRoot_nonneg t)]
  rw [h.deriv,hs]
  change |2*psiRoot t*deriv psiRoot t|≤(2*B)*psiRoot t
  have hn : 0≤(2:ℝ)*psiRoot t := mul_nonneg (by norm_num) (psiRoot_nonneg t)
  rw [abs_mul,abs_of_nonneg hn]
  exact (mul_le_mul_of_nonneg_left (hb t) hn).trans_eq (by ring)

end Bilevel.PolishedLiteral
