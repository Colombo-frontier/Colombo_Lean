import Bilevel.PolishedLiteralSquareRoot
import Bilevel.PolishedLiteralWrappedSelectors

/-! Source-faithful square-root derivative envelopes. Unlike the capped
implementation the selector range is [0, exp(1)], so sqrt(exp(1)) is
retained in every product estimate. -/
noncomputable section
namespace Bilevel.PolishedLiteral
open ChiBoundedChain ZeroChainPotential ChiRecursive

theorem bounded_mul_sqrt_le {a b M : ℝ} (ha : 0≤a) (_hb : 0≤b) (hM : a≤M) :
    a*Real.sqrt b≤Real.sqrt M*Real.sqrt (a*b) := by
  have he : Real.sqrt a*Real.sqrt a=a := Real.mul_self_sqrt ha
  calc
    a*Real.sqrt b=(Real.sqrt a*Real.sqrt a)*Real.sqrt b := by rw [he]
    _ = Real.sqrt a*(Real.sqrt a*Real.sqrt b) := by ring
    _ ≤ Real.sqrt M*(Real.sqrt a*Real.sqrt b) :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hM) (by positivity)
    _ = Real.sqrt M*Real.sqrt (a*b) := by rw [Real.sqrt_mul ha]

theorem selector_sqrt_derivative : ∃ C : ℝ,0≤C ∧
    ∀ (n : ℕ) (i : Fin (n+1)) (z : Space n),
      ‖selectorDerivative n i z‖≤C*Real.sqrt (selector n i z) := by
  obtain ⟨B,hB,hb⟩ := psi_sqrt_derivative
  obtain ⟨C,hC,hc⟩ := ChiBoundedChain.mask_sqrt_derivative
  let Q := Real.sqrt (Real.exp 1)
  have hQ : 1≤Q := Real.one_le_sqrt.mpr (Real.one_le_exp (by norm_num))
  have hCQ : C≤B+C*Q := by nlinarith
  refine ⟨B+C*Q,by positivity,fun n i z => ?_⟩
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (hc n 0 z).trans (mul_le_mul_of_nonneg_right hCQ (Real.sqrt_nonneg _))
  · let a := psi (z j.castSucc)
    let b := tailMask j.succ z
    have ha : 0≤a := psi_nonneg _
    have haM : a≤Real.exp 1 := psi_le_exp_one _
    have hb' : 0≤b ∧ b≤1 := tailMask_range _ _
    have h₁ := mul_le_mul_of_nonneg_right (hb (z j.castSucc)) hb'.1
    have h₂ := mul_le_mul_of_nonneg_left (hc n j.succ z) ha
    have hterm : ‖(deriv psi (z j.castSucc)*b) •
        EuclideanSpace.proj (𝕜:=ℝ) j.castSucc‖≤(B*Real.sqrt a)*b := by
      apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hb'.1]
      exact (mul_le_mul_of_nonneg_left (ZeroChainResidualBounds.projection_norm_le _)
        (mul_nonneg (abs_nonneg _) hb'.1)).trans (by simpa only [mul_one] using h₁)
    have hterm₂ : ‖a • maskDerivative j.succ z‖≤a*(C*Real.sqrt b) := by
      apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
      rw [Real.norm_eq_abs,abs_of_nonneg ha]
      exact h₂
    have hsmall₁ := mul_le_mul_of_nonneg_left (unit_mul_sqrt_le ha hb'.1 hb'.2) hB
    have hsmall₂ := mul_le_mul_of_nonneg_left (bounded_mul_sqrt_le ha hb'.1 haM) hC
    change ‖(deriv psi (z j.castSucc)*b) • EuclideanSpace.proj (𝕜:=ℝ) j.castSucc+
      a • maskDerivative j.succ z‖≤(B+C*Q)*Real.sqrt (a*b)
    dsimp only [Q] at *
    exact (norm_add_le _ _).trans (by nlinarith only [hterm,hterm₂,hsmall₁,hsmall₂])

theorem residualTerm_sqrt_derivative : ∃ C : ℝ,0≤C ∧
    ∀ (n : ℕ) (i : Fin (n+1)) (z : Space n),
      ‖residualTermDerivative n i z‖≤C*Real.sqrt (selector n i z) := by
  obtain ⟨B,hB,hb⟩ := selector_sqrt_derivative
  let P := Real.sqrt (Real.exp 1)
  have hP : 0≤P := Real.sqrt_nonneg _
  refine ⟨gaussianBound*B+P*P,by have := gaussianBound_nonneg;positivity,fun n i z => ?_⟩
  have hs := selector_nonneg n i z
  have hp : |phi (z i)|≤gaussianBound := by
    rw [abs_of_nonneg (phi_nonneg _)];exact phi_bounded _
  have hp' : |phiSlope (z i)|≤P := by simpa only [phi_deriv] using phi_first_bound (z i)
  have h₁ : ‖(-phi (z i)) • selectorDerivative n i z‖≤gaussianBound*(B*Real.sqrt (selector n i z)) := by
    apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
    rw [Real.norm_eq_abs,abs_neg]
    exact mul_le_mul hp (hb n i z) (norm_nonneg _) gaussianBound_nonneg
  have h₂ : ‖(-selector n i z*phiSlope (z i)) • EuclideanSpace.proj (𝕜:=ℝ) i‖≤
      (P*P)*Real.sqrt (selector n i z) := by
    apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
    rw [Real.norm_eq_abs,abs_mul,abs_neg,abs_of_nonneg hs]
    have hh := mul_le_mul_of_nonneg_left (ZeroChainResidualBounds.projection_norm_le i)
      (mul_nonneg hs (abs_nonneg (phiSlope (z i))))
    simp only [mul_one] at hh
    have hl := mul_le_mul_of_nonneg_left hp' hs
    have hr : selector n i z≤P*Real.sqrt (selector n i z) := by
      have h := bounded_mul_sqrt_le hs (by norm_num : (0:ℝ)≤1) (selector_le_exp_one n i z)
      simpa only [Real.sqrt_one,mul_one] using h
    have hr' := mul_le_mul_of_nonneg_right hr hP
    exact hh.trans (by nlinarith only [hl,hr'])
  exact (norm_add_le _ _).trans (by nlinarith only [h₁,h₂])

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem constructed_literal_derivative_envelopes : ∃ Cs Cr : ℝ,0≤Cs ∧ 0≤Cr ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (D : Node E),0≤D.ell → 0<D.width → 0<D.radius → ∀ i u,
      ‖fderiv ℝ (wrappedSelector D i) u‖≤(Cs/D.width)*Real.sqrt (wrappedSelector D i u) ∧
      ‖fderiv ℝ (wrappedResidual D i) u‖≤Cr*(D.ell*D.width)*Real.sqrt (wrappedSelector D i u) := by
  obtain ⟨Cs,hCs,hs⟩ := selector_sqrt_derivative
  obtain ⟨Cr,hCr,hr⟩ := residualTerm_sqrt_derivative
  refine ⟨Cs,Cr,hCs,hCr,fun E _ _ _ D hell hh hR i u => ?_⟩
  constructor
  · rw [(wrappedSelector_hasFDerivAt D i u).fderiv]
    calc
      _ ≤ ‖selectorDerivative D.n i (D.width⁻¹ • D.coordinates u)‖*‖D.normalizedDerivative u‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (Cs*Real.sqrt (wrappedSelector D i u))*(1/D.width) :=
        mul_le_mul (hs _ _ _) (D.normalizedDerivative_norm hh hR u) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · rw [(wrappedResidual_hasFDerivAt D i u).fderiv,
      norm_smul (D.ell*D.width^2) ((residualTermDerivative D.n i (D.width⁻¹ • D.coordinates u)).comp (D.normalizedDerivative u)),Real.norm_eq_abs,
      abs_of_nonneg (show 0≤D.ell*D.width^2 by positivity)]
    calc
      _ ≤ (D.ell*D.width^2)*(‖residualTermDerivative D.n i (D.width⁻¹ • D.coordinates u)‖*‖D.normalizedDerivative u‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (by positivity)
      _ ≤ (D.ell*D.width^2)*((Cr*Real.sqrt (wrappedSelector D i u))*(1/D.width)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (hr _ _ _) (D.normalizedDerivative_norm hh hR u) (norm_nonneg _) (by positivity)) (by positivity)
      _ = _ := by field_simp;ring

end Bilevel.PolishedLiteral
