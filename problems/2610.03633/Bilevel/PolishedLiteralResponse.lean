import Bilevel.PolishedLiteralFormulas
import Bilevel.PolishedLiteralResidualBounds
import Bilevel.ZeroChainSchedule

/-! The actual selected one-sided residual lies in every linear normal
core under the source smallness condition. Together with a quantitative
Hessian budget, this yields the exact unique lower response. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open scoped BigOperators
namespace Bilevel.PolishedLiteral
open PrimitiveGeometry ChiBoundedChain ZeroChainSchedule

theorem selected_residual_value_bound : ∃ C : ℝ,1≤C ∧
    ∀ (X U : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
      [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
      (P : Parameters (X:=X) (U:=U)),0≤P.L → ∀ z : Joint X U,
      |P.selectedResidual z|≤C*P.L*P.β^2 := by
  obtain ⟨C,hC,hc⟩ := normalizedResidual_jet_bounds
  refine ⟨Real.exp 1*C,by have he := Real.one_le_exp (by norm_num : (0:ℝ)≤1);nlinarith,fun X U _ _ _ _ _ _ P hL z => ?_⟩
  have hr (i : Fin (P.macroNode.n+1)) : |P.microResidual i z.snd|≤C*P.L*P.β^2 := by
    have h := hc P.n 0 (by omega) (P.β⁻¹ • P.coordinates i z.snd)
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at h
    change |(P.L*P.β^2)*normalizedResidual P.n _|≤_
    rw [abs_mul,abs_of_nonneg (mul_nonneg hL (sq_nonneg _))]
    exact (mul_le_mul_of_nonneg_left h (mul_nonneg hL (sq_nonneg _))).trans_eq (by ring)
  have hs := PolishedLiteral.selector_sum_le_exp_one P.macroNode.n
    (P.macroNode.width⁻¹ • P.macroNode.coordinates z.fst)
  calc
    |P.selectedResidual z|≤∑ i : Fin (P.macroNode.n+1),
        |PolishedLiteral.wrappedSelector P.macroNode i z.fst*P.microResidual i z.snd| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (P.macroNode.n+1),PolishedLiteral.wrappedSelector P.macroNode i z.fst*(C*P.L*P.β^2) := by
      apply Finset.sum_le_sum
      intro i _
      have hψ := PolishedLiteral.selector_nonneg P.macroNode.n i
        (P.macroNode.width⁻¹ • P.macroNode.coordinates z.fst)
      change 0≤PolishedLiteral.wrappedSelector P.macroNode i z.fst at hψ
      rw [abs_mul,abs_of_nonneg hψ]
      exact mul_le_mul_of_nonneg_left (hr i) hψ
    _ = (∑ i : Fin (P.macroNode.n+1),PolishedLiteral.wrappedSelector P.macroNode i z.fst)*(C*P.L*P.β^2) :=
      (Finset.sum_mul ..).symm
    _ ≤ Real.exp 1*(C*P.L*P.β^2) := mul_le_mul_of_nonneg_right hs (by positivity : 0≤C*P.L*P.β^2)
    _ = _ := by ring

namespace Parameters
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (P : Parameters (X:=X) (U:=U))

theorem normal_core (C c θ : ℝ) (_hC : 0≤C) (hc : 0<c) (hθ : 1≤θ)
    (hL : 0<P.L) (hβ : 0<P.β) (hJ : P.J=levels θ)
    (hw : ∀ j,P.w j=width c P.β θ j)
    (hr : ∀ z,|P.selectedResidual z|≤C*P.L*P.β^2)
    (hsmall : 4*C*P.β*θ≤c) (z : Joint X U) (j : ℕ) (hj : j≤P.J) :
    |P.data.r z/P.data.L|≤P.data.w j/4 := by
  have hθ0 : 0<θ := lt_of_lt_of_le zero_lt_one hθ
  have hb : |P.selectedResidual z/P.L|≤C*P.β^2 := by
    rw [abs_div,abs_of_pos hL]
    apply (div_le_iff₀ hL).mpr
    exact (hr z).trans_eq (by ring)
  have hf := (final_width_bounds c P.β θ hc.le hβ.le hθ).1
  have hm := width_antitone c P.β θ hc.le hβ.le hθ j (levels θ) (by simpa only [hJ] using hj)
  have hn : C*P.β^2≤(c*P.β/θ)/4 := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<4)).mpr
    apply (le_div_iff₀ hθ0).mpr
    nlinarith [mul_le_mul_of_nonneg_right hsmall hβ.le]
  change |P.selectedResidual z/P.L|≤P.w j/4
  rw [hw]
  exact hb.trans (hn.trans (by linarith))

theorem exact_unique_response (hμ : 0<P.μ) (hμL : P.μ≤P.L)
    (hpert : ∀ y,‖iteratedFDeriv ℝ 2 P.data.perturbation y‖≤P.μ/2)
    (hcore : ∀ z j,j≤P.J → |P.selectedResidual z/P.L|≤P.w j/4)
    (x : X) (v : U) :
    (∀ y,PolishedLiteralJointMean.lower P.data x v (PolishedLiteralJointMean.response P.data x v)≤
      PolishedLiteralJointMean.lower P.data x v y) ∧
    (∀ y,PolishedLiteralJointMean.lower P.data x v y≤
      PolishedLiteralJointMean.lower P.data x v (PolishedLiteralJointMean.response P.data x v) →
      y=PolishedLiteralJointMean.response P.data x v) :=
  ⟨PolishedLiteralJointMean.response_minimizes P.data hμ hμL hpert hcore x v,
    PolishedLiteralJointMean.response_unique P.data hμ hμL hpert hcore x v⟩

end Parameters
end Bilevel.PolishedLiteral
