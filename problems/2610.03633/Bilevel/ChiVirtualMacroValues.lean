import Bilevel.ChiVirtualOuter
import Bilevel.ChiVirtualNodeValues

/-! The one-sided outer selectors obey the same exact disclosed-prefix
evaluation identity, proved from their actual first derivative cases. -/
noncomputable section
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive

theorem outer_selector_gradient_small (n : ℕ) (i k : Fin (n+1)) (z : Space n)
    (hk : |z k|≤1/4) : gradient (ChiOuter.selector n i) z k=0 := by
  rw [ZeroChainResidualLocality.gradient_coordinate_eq (ChiOuter.selector_hasFDerivAt n i z)]
  rcases ChiOuter.selector_jet_cases n i z with hz|he
  · rw [hz.2]
    rfl
  · rw [he.2]
    exact selectorDerivative_basis_small i k z hk

theorem outer_normalized_selector_gradient_small (n : ℕ) (h : ℝ) (hh : 0<h)
    (i k : Fin (n+1)) (z : Space n) (hk : |z k|≤h/4) :
    gradient (fun w => ChiOuter.selector n i (h⁻¹ • w)) z k=0 := by
  have he : (fun w => ChiOuter.selector n i (h⁻¹ • w))=
      ZeroChainResidualScaled.scaled (ChiOuter.selector n i) 1 h := by
    funext w
    simp only [ZeroChainResidualScaled.scaled,one_mul]
  rw [he,ZeroChainResidualScaled.scaled_gradient
    ((ChiOuter.selector_contDiff n 3 i).differentiable (by norm_num)),PiLp.smul_apply,
    outer_selector_gradient_small n i k _ (ZeroChainResidualScaled.scaled_coordinate_small h hh z k hk),smul_zero]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem actual_outerSelector_eq_virtual (M : Node E) (rM : ℕ) (columns : Fin (M.n+1) → E)
    (hprefix : ∀ k : Fin (M.n+1),k.val<rM → columns k=M.frame (basis k))
    (hh : 0<M.width) (i : Fin (M.n+1)) (u : E)
    (hz : ∀ k : Fin (M.n+1),rM≤k.val → |M.coordinates u k|≤M.width/4) :
    ChiOuter.wrappedSelector M i u=virtualOuterSelector M rM columns i u := by
  unfold virtualOuterSelector
  rw [readout_eq_retained M.n rM M.radius columns M.frame hprefix]
  exact value_eq_retain _ (((ChiOuter.selector_contDiff M.n 3 i).comp
    (contDiff_id.const_smul M.width⁻¹)).differentiable (by norm_num))
    (fun w hw k hk => outer_normalized_selector_gradient_small M.n M.width hh i k w (hw k hk))
    (M.coordinates u) hz

end Bilevel.ChiPrefixEvaluation
