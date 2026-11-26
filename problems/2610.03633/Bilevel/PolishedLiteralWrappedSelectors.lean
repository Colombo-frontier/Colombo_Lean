import Bilevel.PolishedLiteralSelectors
import Bilevel.PolishedLiteralMacro
import Bilevel.ChiRecursiveJointObjective
import Bilevel.ChiRecursiveNodeDerivative

/-! Actual one-sided selectors composed with the source frame, radial map,
and width normalization. `Node` is used only as a geometry record here;
the functions below are the one-sided macro functions, not its inner payload. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.PolishedLiteral
open ChiBoundedChain ChiRecursive ZeroChainPotential RadialWrapper
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

theorem wrappedSelector_range (D : Node E) (i : Fin (D.n+1)) (u : E) :
    0≤wrappedSelector D i u ∧ wrappedSelector D i u≤Real.exp 1 :=
  ⟨selector_nonneg _ _ _,selector_le_exp_one _ _ _⟩

theorem wrappedSelector_unique (D : Node E) (i j : Fin (D.n+1)) (u : E)
    (hi : wrappedSelector D i u≠0) (hj : wrappedSelector D j u≠0) : i=j :=
  selector_unique i j _ hi hj

theorem wrappedSelector_sum (D : Node E) (u : E) : ∑ i,wrappedSelector D i u≤Real.exp 1 :=
  selector_sum_le_exp_one _ _

theorem macro_contDiff (M : Node E) (ν : ℝ) (k : ℕ) :
    ContDiff ℝ k (macroValue M.n M.ell M.width ν M.radius M.frame) :=
  ((chain_contDiff M.n M.ell M.width k).comp
    (M.frame.toContinuousLinearMap.adjoint.contDiff.comp (compress_contDiff M.radius k))).add
      (full_bowl_contDiff ν M.radius k)

theorem wrappedResidual_nonpos (D : Node E) (hℓ : 0≤D.ell) (i : Fin (D.n+1)) (u : E) :
    wrappedResidual D i u≤0 :=
  mul_nonpos_of_nonneg_of_nonpos (by positivity) (residualTerm_nonpos _ _ _)

theorem wrappedResidual_abs_bound (D : Node E) (hℓ : 0≤D.ell) (i : Fin (D.n+1)) (u : E) :
    |wrappedResidual D i u|≤gaussianBound*(D.ell*D.width^2)*wrappedSelector D i u := by
  unfold wrappedResidual
  rw [abs_mul,abs_of_nonneg (show 0≤D.ell*D.width^2 by positivity)]
  convert mul_le_mul_of_nonneg_left (residualTerm_abs_bound D.n i (D.width⁻¹ • D.coordinates u))
    (show 0≤D.ell*D.width^2 by positivity) using 1
  dsimp only [wrappedSelector]
  ring

theorem wrapped_inactive (D : Node E) (i : Fin (D.n+1)) (u : E)
    (hi : wrappedSelector D i u=0) : wrappedResidual D i u=0 ∧
      fderiv ℝ (wrappedSelector D i) u=0 ∧ fderiv ℝ (wrappedResidual D i) u=0 := by
  have hs : selector D.n i (D.width⁻¹ • D.coordinates u)=0 := hi
  have hd := selectorDerivative_zero_of_zero i _ hs
  rw [(wrappedSelector_hasFDerivAt D i u).fderiv,(wrappedResidual_hasFDerivAt D i u).fderiv]
  simp only [wrappedResidual,residualTerm,residualTermDerivative,hs,hd,neg_zero,
    zero_mul,mul_zero,smul_zero,zero_smul,add_zero,ContinuousLinearMap.zero_comp]
  simp

end Bilevel.PolishedLiteral
