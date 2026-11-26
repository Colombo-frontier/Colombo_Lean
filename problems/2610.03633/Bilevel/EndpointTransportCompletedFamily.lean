import Bilevel.EndpointTransportNetworkCompletion
import Bilevel.EndpointTransportCompletionNodes

/-! A single completed frame family, using independent ordinary completions
above the terminal level and one common rotated network frame at the leaves.
All counts, widths and radii stay equal to the source numerical parameters. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open scoped RealInnerProductSpace
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry ChiBoundedChain ChiPrefixEvaluation EndpointTransportMatrix
  TransportHierarchy TransportNetwork ChiTreeProgress ChiHierarchyIndex

def completedHierarchyFamily (counts : ℕ → ℕ) (J D : ℕ)
    (hdim : ∀ j,counts (j+1)+1≤D) (hT : capacity counts (J+1) 0≤D)
    (r : ℕ → List ℕ → ℕ) (columns : ∀ j,List ℕ → Fin (counts (j+1)+1) → Block D)
    (hGram : ∀ j I,PrefixGram (counts (j+1)) (r j I) (columns j I))
    (j : ℕ) (I : List ℕ) : Space (counts (j+1)) →ₗᵢ[ℝ] Block (completionDimension D D) := by
  by_cases hj : j=J
  · subst j
    exact (commonCompletionFrame D D).comp (canonicalCompletionFrame counts J D hT I)
  · exact (completionBlockEquiv D D).toLinearIsometry.comp
      (completionFrame (counts (j+1)) (r j I) (columns j I)
        (auxiliaryFrame (counts (j+1)) (D+1) ((hdim j).trans (Nat.le_succ D))) (hGram j I))

theorem completedHierarchyFamily_terminal (counts : ℕ → ℕ) (J D : ℕ)
    (hdim : ∀ j,counts (j+1)+1≤D) (hT : capacity counts (J+1) 0≤D)
    (r : ℕ → List ℕ → ℕ) (columns : ∀ j,List ℕ → Fin (counts (j+1)+1) → Block D)
    (hGram : ∀ j I,PrefixGram (counts (j+1)) (r j I) (columns j I)) (I : List ℕ) :
    completedHierarchyFamily counts J D hdim hT r columns hGram J I=
      (commonCompletionFrame D D).comp (canonicalCompletionFrame counts J D hT I) := by
  simp [completedHierarchyFamily]

theorem completedHierarchyFamily_ordinary_coordinates (counts : ℕ → ℕ) (J D : ℕ)
    (hdim : ∀ j,counts (j+1)+1≤D) (hT : capacity counts (J+1) 0≤D)
    (r : ℕ → List ℕ → ℕ) (columns : ∀ j,List ℕ → Fin (counts (j+1)+1) → Block D)
    (hGram : ∀ j I,PrefixGram (counts (j+1)) (r j I) (columns j I))
    (j : ℕ) (hj : j<J) (I : List ℕ) (R : ℝ) (x : Block D) :
    WrappedChain.coordinates (counts (j+1)) R
      (completedHierarchyFamily counts J D hdim hT r columns hGram j I)
      (completionBlockInclusion D D x)=readout (counts (j+1)) (r j I) R (columns j I) x := by
  rw [completedHierarchyFamily,dif_neg (ne_of_lt hj)]
  change WrappedChain.coordinates _ R ((completionBlockEquiv D D).toLinearIsometry.comp
    (completionFrame _ _ _ _ _)) (completionBlockEquiv D D (pack x 0))=_
  exact (coordinates_isometry (completionBlockEquiv D D).toLinearIsometry _ R (pack x 0)).trans
    (completion_coordinates _ _ R _ _ _ x)

def completedMacroFrame (a D : ℕ) (hdim : a+1≤D) (r : ℕ)
    (columns : Fin (a+1) → Block D) (hGram : PrefixGram a r columns) :
    Space a →ₗᵢ[ℝ] Block (completionDimension D D) :=
  (completionBlockEquiv D D).toLinearIsometry.comp
    (completionFrame a r columns (auxiliaryFrame a (D+1) (hdim.trans (Nat.le_succ D))) hGram)

theorem completedMacroFrame_coordinates (a D : ℕ) (hdim : a+1≤D) (r : ℕ)
    (columns : Fin (a+1) → Block D) (hGram : PrefixGram a r columns) (R : ℝ) (x : Block D) :
    WrappedChain.coordinates a R (completedMacroFrame a D hdim r columns hGram)
      (completionBlockInclusion D D x)=readout a r R columns x := by
  change WrappedChain.coordinates _ R ((completionBlockEquiv D D).toLinearIsometry.comp
    (completionFrame _ _ _ _ _)) (completionBlockEquiv D D (pack x 0))=_
  exact (coordinates_isometry (completionBlockEquiv D D).toLinearIsometry _ R (pack x 0)).trans
    (completion_coordinates _ _ R _ _ _ x)

end Bilevel.EndpointTransportResponse
