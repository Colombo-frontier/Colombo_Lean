import Bilevel.ChiVirtualRecursion
import Bilevel.ChiRecursiveNodeLocality

/-! Joint continuity in disclosed vector arrays and query blocks for the
explicit virtual recursive scalar formulas. The data may contain all node
prefixes; each evaluation still reads only a finite recursive tree. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem virtualH_continuous (D : Node E) (r : ℕ) :
    Continuous (fun p : (Fin (D.n+1) → E) × E => virtualH D r p.1 p.2) :=
  (payload_contDiff D.n D.ell D.width D.receiver D.nu D.force D.parentWidth D.tailRadius 3).continuous.comp
    (readout_continuous D.n r D.radius)

theorem virtualSelector_continuous (D : Node E) (r : ℕ) (i : Fin (D.n+1)) :
    Continuous (fun p : (Fin (D.n+1) → E) × E => virtualSelector D r p.1 i p.2) :=
  (selector_contDiff D.n 3 i).continuous.comp ((readout_continuous D.n r D.radius).const_smul D.width⁻¹)

theorem virtualResidual_continuous (D : Node E) (r : ℕ) (i : Fin (D.n+1)) :
    Continuous (fun p : (Fin (D.n+1) → E) × E => virtualResidual D r p.1 i p.2) :=
  (Rterm_contDiff D.n D.ell D.width i 3).continuous.comp (readout_continuous D.n r D.radius)

theorem virtualRelease_continuous (D : Node E) (r : ℕ) :
    Continuous (fun p : (Fin (D.n+1) → E) × E => virtualRelease D r p.1 p.2) := by
  apply (releaseGate_contDiff (k:=3)).continuous.comp
  exact (((EuclideanSpace.proj (𝕜:=ℝ) (Fin.last D.n)).continuous.comp
    (readout_continuous D.n r D.radius)).div_const D.parentWidth)

abbrev ColumnData (D : Geometry E) := ∀ j I,Fin ((D j I).n+1) → E

theorem nodeData_continuous (D : Geometry E) (j : ℕ) (I : List ℕ) :
    Continuous (fun p : ColumnData D × (ℕ → E) => (p.1 j I,p.2 j)) := by
  have hj : Continuous (fun p : ColumnData D × (ℕ → E) => p.1 j) :=
    (continuous_apply j).comp continuous_fst
  have hI : Continuous (fun p : ColumnData D × (ℕ → E) => p.1 j I) :=
    (continuous_apply I).comp hj
  exact hI.prodMk ((continuous_apply j).comp continuous_snd)

theorem nodeZeroData_continuous (D : Geometry E) (j : ℕ) (I : List ℕ) :
    Continuous (fun p : ColumnData D × (ℕ → E) => (p.1 j I,(0:E))) :=
  (nodeData_continuous D j I).fst.prodMk continuous_const

end Bilevel.ChiPrefixEvaluation
