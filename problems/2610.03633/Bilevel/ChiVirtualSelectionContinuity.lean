import Bilevel.ChiVirtualContinuity
import Bilevel.ChiVirtualSelection

noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem readout_data_continuous (D : Geometry E) (r : ℕ → List ℕ → ℕ) (j : ℕ) (I : List ℕ) :
    Continuous (fun p : ColumnData D × (ℕ → E) => readout (D j I).n (r j I) (D j I).radius (p.1 j I) (p.2 j)) := by
  exact Continuous.comp (f := fun p : ColumnData D × (ℕ → E) => (p.1 j I,p.2 j))
    (g := fun p : (Fin ((D j I).n+1) → E) × E => readout (D j I).n (r j I) (D j I).radius p.1 p.2)
    (readout_continuous (D j I).n (r j I) (D j I).radius) (nodeData_continuous D j I)

theorem virtualSelect_continuous (D : Geometry E) (r : ℕ → List ℕ → ℕ)
    (leaf : ∀ j I,Space (D j I).n → ℝ) (hl : ∀ j I,Continuous (leaf j I))
    (d j : ℕ) (I : List ℕ) :
    Continuous (fun p : ColumnData D × (ℕ → E) => virtualSelect D r p.1 leaf d j I p.2) := by
  induction d generalizing j I with
  | zero =>
    dsimp only [virtualSelect]
    exact Continuous.comp (f := fun p : ColumnData D × (ℕ → E) =>
      readout (D j I).n (r j I) (D j I).radius (p.1 j I) (p.2 j))
      (g := leaf j I) (hl j I) (readout_data_continuous D r j I)
  | succ d ih =>
    dsimp only [virtualSelect]
    exact continuous_finset_sum _ (fun i _ =>
      (virtualSelector_data_continuous D r j I i).mul (ih (j+1) (child I i.val)))

theorem padded_continuous (m : ℕ) : Continuous (padded (E:=E) (m:=m)) :=
  continuous_pi (fun j => (block (E:=E) m j).continuous)

end Bilevel.ChiPrefixEvaluation
