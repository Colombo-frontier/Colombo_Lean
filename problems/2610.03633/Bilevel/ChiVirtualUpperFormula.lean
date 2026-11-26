import Bilevel.ChiOuterUpperBase
import Bilevel.ChiVirtualCoarseValues

/-! Explicit upper-base evaluator. It uses only numeric node parameters,
disclosed columns, and the original query. The macro chain and release
correction are retained together; neither term alone is prefix-local. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiOuter
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def virtualMacroValue (M : Node E) (ν : ℝ) (rM : ℕ)
    (macroColumns : Fin (M.n+1) → E) (u : E) : ℝ :=
  ChiOuter.chain M.n M.ell M.width (readout M.n rM M.radius macroColumns u)+
    RadialWrapper.bowl ν M.radius u

def virtualOuterResidual (M : Node E) (rM : ℕ) (macroColumns : Fin (M.n+1) → E)
    (i : Fin (M.n+1)) (u : E) : ℝ :=
  (M.ell*M.width^2)*ChiOuter.residualTerm M.n i
    (M.width⁻¹ • readout M.n rM M.radius macroColumns u)

def virtualOuterReleaseCorrection (m : ℕ) (M : Node E) (D : Geometry F)
    (rM : ℕ) (r : ℕ → List ℕ → ℕ) (macroColumns : Fin (M.n+1) → E)
    (columns : ∀ j I,Fin ((D j I).n+1) → F) (z : Joint E (Blocks m F)) : ℝ :=
  ∑ i : Fin (M.n+1),virtualOuterResidual M rM macroColumns i z.fst *
    (virtualRelease (D 0 [i.val]) (r 0 [i.val]) (columns 0 [i.val]) (block m 0 z.snd)-1)

def virtualUpperBase (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (d : ℕ) (ρ R : ℝ)
    (rM : ℕ) (r : ℕ → List ℕ → ℕ) (macroColumns : Fin (M.n+1) → E)
    (columns : ∀ j I,Fin ((D j I).n+1) → F) (z : Joint E (Blocks m F)) : ℝ :=
  virtualMacroValue M ν rM macroColumns z.fst+
    (virtualOuterReleaseCorrection m M D rM r macroColumns columns z+
      virtualOuterCarrier m M D rM r macroColumns columns d 0 z+baseRadial m ρ R z)

end Bilevel.ChiPrefixEvaluation
