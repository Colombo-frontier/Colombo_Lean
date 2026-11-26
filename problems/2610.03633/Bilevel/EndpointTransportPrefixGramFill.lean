import Bilevel.EndpointTransportVirtualData
import Bilevel.PrefixGramMeasurable

/-! Proof-only filling of ordinary arrays that the physical hierarchy never
reads. No Gram requirement is imposed on terminal or deeper input arrays. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.EndpointTransportResponse
open ChiBoundedChain ChiRecursive ChiPrefixEvaluation
set_option autoImplicit false
set_option maxHeartbeats 400000

def filledOrdinaryColumns {D : ℕ} (G : Geometry (Block D)) (J : ℕ) (C : ColumnData G) : ColumnData G :=
  fun j I => if j<J then C j I else fun a => (G j I).frame (basis a)

theorem filledOrdinaryColumns_relevant {D : ℕ} (G : Geometry (Block D)) (J : ℕ) (C : ColumnData G)
    (j : ℕ) (I : List ℕ) (hj : j<J) : filledOrdinaryColumns G J C j I=C j I := by
  simp only [filledOrdinaryColumns,if_pos hj]

theorem filledOrdinaryColumns_gram {D : ℕ} (G : Geometry (Block D)) (J : ℕ)
    (C : ColumnData G) (r : ℕ → List ℕ → ℕ)
    (hC : ∀ j I,j<J → PrefixGram (G j I).n (r j I) (C j I)) :
    ∀ j I,PrefixGram (G j I).n (r j I) (filledOrdinaryColumns G J C j I) := by
  intro j I
  by_cases hj : j<J
  · rw [filledOrdinaryColumns_relevant G J C j I hj]
    exact hC j I hj
  · intro a b _ _
    simp only [filledOrdinaryColumns,if_neg hj,(G j I).frame.inner_map_map]
    simp [basis,EuclideanSpace.inner_single_left,EuclideanSpace.single_apply]

end Bilevel.EndpointTransportResponse
