import Bilevel.PolishedLiteralWrappedSelectors
import Bilevel.PolishedLiteralMacro


/-! Actual outer attachment and exact transport to the selected inner
recursive objective. Every public radial penalty remains outside selectors. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.PolishedLiteral
open ChiBoundedChain ChiRecursive
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def attachment (M : Node E) (ν : ℝ) (Q W : Fin (M.n+1) → ℝ) (x : E) : ℝ :=
  macroValue M.n M.ell M.width ν M.radius M.frame x +
    ∑ i, ((Q i-1)*wrappedResidual M i x + W i*wrappedSelector M i x)

def outerPerturbation (M : Node E) (Q W : Fin (M.n+1) → ℝ) (x : E) : E →L[ℝ] ℝ :=
  ∑ i, ((Q i-1) • fderiv ℝ (wrappedResidual M i) x + W i • fderiv ℝ (wrappedSelector M i) x)

theorem attachment_fderiv (M : Node E) (ν : ℝ) (Q W : Fin (M.n+1) → ℝ)
    (hR : 0 < M.radius) (x : E) :
    fderiv ℝ (attachment M ν Q W) x =
      fderiv ℝ (macroValue M.n M.ell M.width ν M.radius M.frame) x + outerPerturbation M Q W x := by
  have hm := (macro_hasGradientAt M.n M.ell M.width ν M.radius hR M.frame x).hasFDerivAt
  have hd (i : Fin (M.n+1)) :
      HasFDerivAt (fun t => (Q i-1)*wrappedResidual M i t+W i*wrappedSelector M i t)
        ((Q i-1) • fderiv ℝ (wrappedResidual M i) x+W i • fderiv ℝ (wrappedSelector M i) x) x :=
    (((wrappedResidual_contDiff M i 1).differentiable (by norm_num) x).hasFDerivAt.const_mul (Q i-1)).add
      (((wrappedSelector_contDiff M i 1).differentiable (by norm_num) x).hasFDerivAt.const_mul (W i))
  have hs := HasFDerivAt.sum (fun (i : Fin (M.n+1)) (_ : i ∈ Finset.univ) => hd i)
  rw [hm.fderiv]
  exact (hm.add hs).fderiv

theorem outerPerturbation_eq_active (M : Node E) (Q W : Fin (M.n+1) → ℝ) (x : E)
    (i : Fin (M.n+1)) (hi : wrappedSelector M i x ≠ 0) :
    outerPerturbation M Q W x =
      (Q i-1) • fderiv ℝ (wrappedResidual M i) x + W i • fderiv ℝ (wrappedSelector M i) x := by
  unfold outerPerturbation
  apply Finset.sum_eq_single i
  · intro j _ hji
    have hj : wrappedSelector M j x = 0 := by
      by_contra hj
      exact hji (wrappedSelector_unique M j i x hj hi)
    rw [(wrapped_inactive M j x hj).2.1,(wrapped_inactive M j x hj).2.2]
    simp
  · simp

theorem outerPerturbation_zero (M : Node E) (Q W : Fin (M.n+1) → ℝ) (x : E)
    (hi : ∀ i, wrappedSelector M i x = 0) : outerPerturbation M Q W x = 0 := by
  unfold outerPerturbation
  apply Finset.sum_eq_zero
  intro i _
  rw [(wrapped_inactive M i x (hi i)).2.1,(wrapped_inactive M i x (hi i)).2.2]
  simp

theorem attachment_eq_active (M : Node E) (ν : ℝ) (Q W : Fin (M.n+1) → ℝ) (x : E)
    (i : Fin (M.n+1)) (hi : wrappedSelector M i x ≠ 0) :
    attachment M ν Q W x = macroValue M.n M.ell M.width ν M.radius M.frame x +
      (Q i-1)*wrappedResidual M i x+W i*wrappedSelector M i x := by
  have hs : (∑ j, ((Q j-1)*wrappedResidual M j x+W j*wrappedSelector M j x)) =
      (Q i-1)*wrappedResidual M i x+W i*wrappedSelector M i x := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      have hj : wrappedSelector M j x = 0 := by
        by_contra hj
        exact hji (wrappedSelector_unique M j i x hj hi)
      rw [hj,(wrapped_inactive M j x hj).1]
      ring
    · simp
  unfold attachment
  rw [hs]
  ring


end Bilevel.PolishedLiteral
