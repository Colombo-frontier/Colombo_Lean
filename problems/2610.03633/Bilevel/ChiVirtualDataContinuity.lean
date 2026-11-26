import Bilevel.ChiVirtualNodeContinuity

noncomputable section
set_option maxHeartbeats 200000
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem virtualH_data_continuous (D : Geometry E) (r : ℕ → List ℕ → ℕ) (j : ℕ) (I : List ℕ) :
    Continuous (fun p : ColumnData D × (ℕ → E) => virtualH (D j I) (r j I) (p.1 j I) (p.2 j)) := by
  exact Continuous.comp (f := fun p : ColumnData D × (ℕ → E) => (p.1 j I,p.2 j))
    (g := fun p : (Fin ((D j I).n+1) → E) × E => virtualH (D j I) (r j I) p.1 p.2)
    (virtualH_continuous (D j I) (r j I)) (nodeData_continuous D j I)

theorem virtualH_zero_data_continuous (D : Geometry E) (r : ℕ → List ℕ → ℕ) (j : ℕ) (I : List ℕ) :
    Continuous (fun p : ColumnData D × (ℕ → E) => virtualH (D j I) (r j I) (p.1 j I) 0) := by
  exact Continuous.comp (f := fun p : ColumnData D × (ℕ → E) => (p.1 j I,(0:E)))
    (g := fun p : (Fin ((D j I).n+1) → E) × E => virtualH (D j I) (r j I) p.1 p.2)
    (virtualH_continuous (D j I) (r j I)) (nodeZeroData_continuous D j I)

theorem virtualResidual_data_continuous (D : Geometry E) (r : ℕ → List ℕ → ℕ)
    (j : ℕ) (I : List ℕ) (i : Fin ((D j I).n+1)) :
    Continuous (fun p : ColumnData D × (ℕ → E) => virtualResidual (D j I) (r j I) (p.1 j I) i (p.2 j)) := by
  exact Continuous.comp (f := fun p : ColumnData D × (ℕ → E) => (p.1 j I,p.2 j))
    (g := fun p : (Fin ((D j I).n+1) → E) × E => virtualResidual (D j I) (r j I) p.1 i p.2)
    (virtualResidual_continuous (D j I) (r j I) i) (nodeData_continuous D j I)

theorem virtualSelector_data_continuous (D : Geometry E) (r : ℕ → List ℕ → ℕ)
    (j : ℕ) (I : List ℕ) (i : Fin ((D j I).n+1)) :
    Continuous (fun p : ColumnData D × (ℕ → E) => virtualSelector (D j I) (r j I) (p.1 j I) i (p.2 j)) := by
  exact Continuous.comp (f := fun p : ColumnData D × (ℕ → E) => (p.1 j I,p.2 j))
    (g := fun p : (Fin ((D j I).n+1) → E) × E => virtualSelector (D j I) (r j I) p.1 i p.2)
    (virtualSelector_continuous (D j I) (r j I) i) (nodeData_continuous D j I)

theorem virtualRelease_data_continuous (D : Geometry E) (r : ℕ → List ℕ → ℕ) (j : ℕ) (I : List ℕ) :
    Continuous (fun p : ColumnData D × (ℕ → E) => virtualRelease (D j I) (r j I) (p.1 j I) (p.2 j)) := by
  exact Continuous.comp (f := fun p : ColumnData D × (ℕ → E) => (p.1 j I,p.2 j))
    (g := fun p : (Fin ((D j I).n+1) → E) × E => virtualRelease (D j I) (r j I) p.1 p.2)
    (virtualRelease_continuous (D j I) (r j I)) (nodeData_continuous D j I)

end Bilevel.ChiPrefixEvaluation
