import Bilevel.TransportHierarchyStoreData
import Bilevel.TransportAugmentedPositiveFrames

/-! Every disclosed hierarchy array entry lies in the common analytical
auxiliary space. This holds for arbitrary controller states, before any
validity event; unused entries are zero. -/
noncomputable section
open MeasureTheory
universe u v
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiHierarchyHaar TransportRound
  TransportNetwork EndpointTransportResponse TransportAugmented
set_option autoImplicit false
set_option maxHeartbeats 500000
variable {C : Type u} {S : Type v} [MeasurableSpace C] [MeasurableSpace S]
  {n D p Tnet B : ℕ} (counts : ℕ → ℕ) (J : ℕ)
  (A : Controller C S n D p Tnet (Fintype.card (FrameIndex counts J)) (auxiliaryCapacity counts J) B)
  (t : ℕ)
  (st : CommonState C S (Fintype.card (FrameIndex counts J)) (auxiliaryCapacity counts J) D ×
    Generators n D (size n p 1 1 t))

theorem auxiliaryStoreReadout_mem (i : FrameIndex counts J) (k : Fin (chainSize i+1)) :
    auxiliaryStoreReadout counts J st.1.2.2 i k∈analyticalAuxSpaceAny A t st :=
  analyticalAuxSpaceAny_retained A t st (enumerate counts J i) (auxiliaryColumnIndex counts J i k)

theorem hierarchyOrdinaryReadout_mem (j : ℕ) (I : List ℕ) (k : Fin (counts (j+1)+1)) :
    hierarchyOrdinaryReadout counts J st.1.2.2 j I k∈analyticalAuxSpaceAny A t st := by
  by_cases hj : j<J
  · simp only [hierarchyOrdinaryReadout,dif_pos hj]
    exact auxiliaryStoreReadout_mem counts J A t st
      (Sum.inr (canonicalNode counts J ⟨j,Nat.lt_succ_of_lt hj⟩ I)) k
  · simp only [hierarchyOrdinaryReadout,dif_neg hj,Pi.zero_apply]
    exact Submodule.zero_mem _

theorem hierarchyMacroReadout_mem (k : Fin (counts 0+1)) :
    auxiliaryStoreReadout counts J st.1.2.2 (Sum.inl ()) k∈analyticalAuxSpaceAny A t st :=
  auxiliaryStoreReadout_mem counts J A t st (Sum.inl ()) k

end Bilevel.TransportHierarchy
