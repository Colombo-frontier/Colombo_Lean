import Bilevel.PolishedLiteralCouplingBudgets
import Bilevel.MultiscalePerturbation

/-! Actual square-compensation and normal-coupling budgets for the literal
hierarchical mean. No second/third perturbation bound is assumed. -/
noncomputable section
namespace Bilevel.PolishedLiteral
open PrimitiveGeometry ChiBoundedChain ZeroChainSchedule ZeroChainResidualBounds
open PolishedLiteralCompensated
open MultiscaleMean (square_jet_bound const_mul_jet_norm)
namespace Parameters
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
variable (P : Parameters (X:=X) (U:=U))

def compensation (y : PolishedLiteralCompensated.LowerSpace (Joint X U)) : ℝ :=
  P.μ/(2*P.L^2)*(P.selectedResidual (uProj (Joint X U) y))^2

theorem compensation_contDiff : ContDiff ℝ 3 P.compensation :=
  contDiff_const.mul ((P.selectedResidual_contDiff.comp (uProj (Joint X U)).contDiff).pow 2)

theorem perturbation_split : P.data.perturbation=fun y =>
    P.compensation y-(P.μ/P.L)*P.data.coupling y := rfl

theorem compensation_bounds (B : ℝ) (hB : 0≤B) (hμ : 0<P.μ) (hL : 0<P.L) (hβ : 0<P.β)
    (hb : ∀ z : Joint X U,∀ k : Fin 4,
      ‖iteratedFDeriv ℝ k.val P.selectedResidual z‖≤B*P.L*P.β^2/P.β^k.val)
    (y : PolishedLiteralCompensated.LowerSpace (Joint X U)) :
    ‖iteratedFDeriv ℝ 2 P.compensation y‖≤2*P.μ*B^2*P.β^2 ∧
    ‖iteratedFDeriv ℝ 3 P.compensation y‖≤4*P.μ*B^2*P.β := by
  let f := P.selectedResidual ∘ uProj (Joint X U)
  have hf : ContDiff ℝ 3 f := P.selectedResidual_contDiff.comp (uProj (Joint X U)).contDiff
  have hjet (l : ℕ) (hl : l≤3) : ‖iteratedFDeriv ℝ l f y‖≤(B*P.L*P.β^2)/P.β^l :=
    (PolishedLiteralCompensated.linear_comp_jet_le P.selectedResidual_contDiff y l hl).trans
      (hb (uProj (Joint X U) y) ⟨l,by omega⟩)
  have hs (k : ℕ) (hk : k≤3) : ‖iteratedFDeriv ℝ k P.compensation y‖≤
      (P.μ/(2*P.L^2))*((2:ℝ)^k*(B*P.L*P.β^2)^2/P.β^k) := by
    have hh := square_jet_bound hf (B*P.L*P.β^2) P.β (by positivity) hβ y k hk
      (fun l hl => hjet l (by omega))
    change ‖iteratedFDeriv ℝ k (fun v => (P.μ/(2*P.L^2))*(f v)^2) y‖≤_
    have he : (fun v => (f v)^2)=fun v => f v*f v := by funext v;ring
    rw [const_mul_jet_norm (hf.pow 2) _ y k hk,abs_of_pos (by positivity : 0<P.μ/(2*P.L^2)),he]
    exact mul_le_mul_of_nonneg_left hh (by positivity)
  constructor
  · apply (hs 2 (by norm_num)).trans_eq
    field_simp
    ring
  · apply (hs 3 (by norm_num)).trans_eq
    field_simp
    ring

end Parameters

/-- Source `hier:eq:K-budgets`, before absorbing the fixed numerical c_ms.
The functions are the literal r,e_j,n_w from the manuscript. -/
theorem actual_literal_perturbation_bounds : ∃ M : ℝ,1≤M ∧
    ∀ (X U : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
      [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
      (P : Parameters (X:=X) (U:=U)) (c θ : ℝ),
      0<c → c≤1/16 → 1≤θ → 0<P.μ → 0<P.L → 0<P.β → P.β≤P.radius →
      P.β≤P.macroNode.width → P.macroNode.width≤P.macroNode.radius →
      P.J=levels θ → P.δ=resolution c P.β θ → P.w=width c P.β θ →
      ∀ y : PolishedLiteralCompensated.LowerSpace (Joint X U),
      ‖iteratedFDeriv ℝ 2 P.data.perturbation y‖≤M*P.μ*(P.β^2+P.β*Real.sqrt θ/c) ∧
      ‖iteratedFDeriv ℝ 3 P.data.perturbation y‖≤M*P.μ*(P.β+θ/c^2) := by
  obtain ⟨B,hB,hb⟩ := selected_residual_joint_jet_bounds
  obtain ⟨K,hK,hk⟩ := actual_literal_coupling_bounds
  let M := 4*B^2+K
  have hM : 1≤M := by dsimp [M];nlinarith [sq_nonneg B]
  have hBM : 4*B^2≤M := by dsimp [M];linarith
  have hKM : K≤M := by dsimp [M];nlinarith [sq_nonneg B]
  refine ⟨M,hM,?_⟩
  intro X U _ _ _ _ _ _ P c θ hc hcs hθ hμ hL hβ hR hβb hbR hJ hδ hw y
  have hcomp := P.compensation_bounds B (by linarith) hμ hL hβ
    (fun z k => hb X U P hL.le hβ hR hβb hbR z k.val (by omega)) y
  have hcoupl := hk X U P c θ hc hcs hθ hL hβ hR hβb hbR hJ hδ hw y
  have hbound (k : ℕ) (hk : k≤3) :
      ‖iteratedFDeriv ℝ k P.data.perturbation y‖≤‖iteratedFDeriv ℝ k P.compensation y‖+
        (P.μ/P.L)*‖iteratedFDeriv ℝ k P.data.coupling y‖ := by
    rw [P.perturbation_split]
    have hscaled : ContDiff ℝ 3 (fun v => (P.μ/P.L)*P.data.coupling v) :=
      contDiff_const.mul P.data.coupling_contDiff
    have hh := jet_sub_norm_le P.compensation_contDiff hscaled y k hk
    rw [const_mul_jet_norm P.data.coupling_contDiff _ y k hk,abs_of_pos (div_pos hμ hL)] at hh
    exact hh
  constructor
  · have hct := mul_le_mul_of_nonneg_left hcoupl.1 (div_nonneg hμ.le hL.le)
    have he : (P.μ/P.L)*(K*P.L*P.β*Real.sqrt θ/c)=K*P.μ*P.β*Real.sqrt θ/c := by field_simp;ring
    rw [he] at hct
    have hK' := mul_le_mul_of_nonneg_right hKM
      (show 0≤P.μ*P.β*Real.sqrt θ/c by positivity)
    have hB' := mul_le_mul_of_nonneg_right (show 2*B^2≤M by nlinarith [sq_nonneg B])
      (show 0≤P.μ*P.β^2 by positivity)
    have hh := hbound 2 (by norm_num)
    have hbcomp := hcomp.1
    simp only [div_eq_mul_inv] at hct hK' hB' hh hbcomp ⊢
    ring_nf at hct hK' hB' hh hbcomp ⊢
    exact hh.trans (add_le_add (hct.trans hK') (hbcomp.trans hB'))
  · have hct := mul_le_mul_of_nonneg_left hcoupl.2 (div_nonneg hμ.le hL.le)
    have he : (P.μ/P.L)*(K*P.L*θ/c^2)=K*P.μ*θ/c^2 := by field_simp;ring
    rw [he] at hct
    have hK' := mul_le_mul_of_nonneg_right hKM (show 0≤P.μ*θ/c^2 by positivity)
    have hB' := mul_le_mul_of_nonneg_right hBM (show 0≤P.μ*P.β by positivity)
    have hh := hbound 3 (by norm_num)
    have hbcomp := hcomp.2
    simp only [div_eq_mul_inv] at hct hK' hB' hh hbcomp ⊢
    ring_nf at hct hK' hB' hh hbcomp ⊢
    exact hh.trans (add_le_add (hct.trans hK') (hbcomp.trans hB'))

end Bilevel.PolishedLiteral
