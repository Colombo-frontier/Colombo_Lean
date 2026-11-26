import Bilevel.ChiOuterSelectors
import Bilevel.ChiRecursiveNodeDerivative

/-! Actual one-sided selectors composed with the source frame, radial map,
and width normalization. `Node` is used only as a geometry record here;
the functions below are the one-sided macro functions, not its inner payload. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ZeroChainPotential
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def wrappedSelector (D : Node E) (i : Fin (D.n+1)) (u : E) : ℝ :=
  selector D.n i (D.width⁻¹ • D.coordinates u)

def wrappedResidual (D : Node E) (i : Fin (D.n+1)) (u : E) : ℝ :=
  (D.ell*D.width^2)*residualTerm D.n i (D.width⁻¹ • D.coordinates u)

theorem wrappedSelector_contDiff (D : Node E) (i : Fin (D.n+1)) (k : ℕ) :
    ContDiff ℝ k (wrappedSelector D i) :=
  (selector_contDiff D.n k i).comp ((D.coordinates_contDiff k).const_smul D.width⁻¹)

theorem wrappedResidual_contDiff (D : Node E) (i : Fin (D.n+1)) (k : ℕ) :
    ContDiff ℝ k (wrappedResidual D i) := by
  have ht : ContDiff ℝ k (residualTerm D.n i) :=
    (selector_contDiff D.n k i).neg.mul
      ((phi_contDiff k).comp (EuclideanSpace.proj (𝕜:=ℝ) i).contDiff)
  exact contDiff_const.mul (ht.comp ((D.coordinates_contDiff k).const_smul D.width⁻¹))

theorem wrappedSelector_hasFDerivAt (D : Node E) (i : Fin (D.n+1)) (u : E) :
    HasFDerivAt (wrappedSelector D i)
      ((selectorDerivative D.n i (D.width⁻¹ • D.coordinates u)).comp (D.normalizedDerivative u)) u :=
  (selector_hasFDerivAt D.n i _).comp u ((D.coordinates_hasFDerivAt u).const_smul D.width⁻¹)

theorem wrappedResidual_hasFDerivAt (D : Node E) (i : Fin (D.n+1)) (u : E) :
    HasFDerivAt (wrappedResidual D i)
      ((D.ell*D.width^2) • (residualTermDerivative D.n i (D.width⁻¹ • D.coordinates u)).comp
        (D.normalizedDerivative u)) u :=
  ((residualTerm_hasFDerivAt D.n i _).comp u
    ((D.coordinates_hasFDerivAt u).const_smul D.width⁻¹)).const_mul (D.ell*D.width^2)

theorem wrappedSelector_jet_cases (D : Node E) (i : Fin (D.n+1)) (u : E) :
    (wrappedSelector D i u = 0 ∧ fderiv ℝ (wrappedSelector D i) u = 0 ∧
      wrappedResidual D i u = 0 ∧ fderiv ℝ (wrappedResidual D i) u = 0) ∨
    (wrappedSelector D i u = D.selector i u ∧
      fderiv ℝ (wrappedSelector D i) u = fderiv ℝ (D.selector i) u ∧
      wrappedResidual D i u = D.residual i u ∧
      fderiv ℝ (wrappedResidual D i) u = fderiv ℝ (D.residual i) u) := by
  rw [(wrappedSelector_hasFDerivAt D i u).fderiv, (wrappedResidual_hasFDerivAt D i u).fderiv,
    (D.selector_hasFDerivAt i u).fderiv, (D.residual_hasFDerivAt i u).fderiv]
  rcases selector_jet_cases D.n i (D.width⁻¹ • D.coordinates u) with h|h
  · left
    simp only [wrappedSelector,wrappedResidual,h.1,h.2,residualTerm,residualTermDerivative,
      smul_zero,neg_zero,zero_mul,zero_smul,add_zero,mul_zero,ContinuousLinearMap.zero_comp]
    simp
  · right
    simp only [wrappedSelector,wrappedResidual,h.1,h.2,residualTerm,residualTermDerivative,
      Node.selector,Node.residual,ChiBoundedChain.Rterm,ZeroChainResidualScaled.scaled,
      ChiBoundedChain.residualTerm,ChiBoundedChain.residualTermDerivative]
    simp

theorem wrappedSelector_range (D : Node E) (i : Fin (D.n+1)) (u : E) :
    0 ≤ wrappedSelector D i u ∧ wrappedSelector D i u ≤ 1 := selector_range _ _ _

theorem wrappedSelector_unique (D : Node E) (i j : Fin (D.n+1)) (u : E)
    (hi : wrappedSelector D i u ≠ 0) (hj : wrappedSelector D j u ≠ 0) : i = j :=
  selector_unique i j _ hi hj

theorem wrappedSelector_sum (D : Node E) (u : E) : ∑ i, wrappedSelector D i u ≤ 1 :=
  selector_sum_le_one _ _

theorem wrappedResidual_nonpos (D : Node E) (hℓ : 0 ≤ D.ell) (i : Fin (D.n+1)) (u : E) :
    wrappedResidual D i u ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos (by positivity) (residualTerm_nonpos _ _ _)

theorem wrappedResidual_abs_bound (D : Node E) (hℓ : 0 ≤ D.ell) (i : Fin (D.n+1)) (u : E) :
    |wrappedResidual D i u| ≤ gaussianBound*(D.ell*D.width^2)*wrappedSelector D i u := by
  unfold wrappedResidual
  rw [abs_mul,abs_of_nonneg (show 0 ≤ D.ell*D.width^2 by positivity)]
  convert mul_le_mul_of_nonneg_left (residualTerm_abs_bound D.n i (D.width⁻¹ • D.coordinates u))
    (show 0 ≤ D.ell*D.width^2 by positivity) using 1
  dsimp only [wrappedSelector]
  ring

theorem wrapped_derivative_bounds_of_node (D : Node E) (Cs Cr : ℝ) (hCs : 0 ≤ Cs) (hCr : 0 ≤ Cr)
    (hell : 0 ≤ D.ell) (hh : 0 < D.width) (i : Fin (D.n+1)) (u : E)
    (hs : ‖fderiv ℝ (D.selector i) u‖ ≤ (Cs/D.width)*Real.sqrt (D.selector i u))
    (hr : ‖fderiv ℝ (D.residual i) u‖ ≤ Cr*(D.ell*D.width)*Real.sqrt (D.selector i u)) :
    ‖fderiv ℝ (wrappedSelector D i) u‖ ≤ (Cs/D.width)*Real.sqrt (wrappedSelector D i u) ∧
    ‖fderiv ℝ (wrappedResidual D i) u‖ ≤ Cr*(D.ell*D.width)*Real.sqrt (wrappedSelector D i u) := by
  rcases wrappedSelector_jet_cases D i u with h|h
  · rw [h.1,h.2.1,h.2.2.2,norm_zero]
    constructor <;> positivity
  · rw [h.1,h.2.1,h.2.2.2]
    exact ⟨hs,hr⟩

end Bilevel.ChiOuter
