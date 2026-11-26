import Bilevel.TransportHierarchyAuxiliaryReadout
import Bilevel.TransportHierarchyEndpointReadout

/-! Explicit observable data for a positive-depth physical hierarchy.
Ancestors come from the auxiliary old store. Terminal endpoint arrays come
from the current prebatch network store; unused latent arrays are zero. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiHierarchyHaar TransportRound
  TransportNetwork EndpointTransportResponse
set_option maxHeartbeats 1200000

abbrev HierarchyStoreData (counts : ℕ → ℕ) (n D : ℕ) :=
  (Fin (counts 0+1) → EuclideanGaussian.Space D) ×
    ((∀ j,List ℕ → Fin (counts (j+1)+1) → EuclideanGaussian.Space D) ×
      ((∀ j,List ℕ → Fin (counts (j+1)+1) → Physical n D) ×
        (∀ j,List ℕ → Fin (counts (j+1)+1) → Physical n D)))

def hierarchyOrdinaryReadout {D : ℕ} (counts : ℕ → ℕ) (J : ℕ)
    (C : TransportAuxiliaryFrame.Store (Fintype.card (FrameIndex counts J)) (auxiliaryCapacity counts J) D)
    (j : ℕ) (I : List ℕ) : Fin (counts (j+1)+1) → EuclideanGaussian.Space D :=
  if hj : j<J then auxiliaryStoreReadout counts J C
    (Sum.inr (canonicalNode counts J ⟨j,Nat.lt_succ_of_lt hj⟩ I)) else 0

def hierarchyEndpointReadout {n D : ℕ} (counts : ℕ → ℕ) (J p t : ℕ)
    (g : Generators (n+1) D (size (n+1) p 1 1 t)) (v : EndpointTransportMatrix.Index n)
    (j : ℕ) (I : List ℕ) : Fin (counts (j+1)+1) → Physical n D :=
  if hj : j=J then by subst j;exact endpointReadout counts J p t g v I else 0

def hierarchyStoreData {n D : ℕ} (counts : ℕ → ℕ) (J p t : ℕ)
    (C : TransportAuxiliaryFrame.Store (Fintype.card (FrameIndex counts J)) (auxiliaryCapacity counts J) D)
    (g : Generators (n+1) D (size (n+1) p 1 1 t)) : HierarchyStoreData counts n D :=
  (auxiliaryStoreReadout counts J C (Sum.inl ()),
    (hierarchyOrdinaryReadout counts J C,
      (hierarchyEndpointReadout counts J p t g 0,
        hierarchyEndpointReadout counts J p t g (Fin.last (n+1)))))

theorem hierarchyStoreData_measurable {n D : ℕ}
    [MeasurableSpace (Physical n D)] [BorelSpace (Physical n D)]
    (counts : ℕ → ℕ) (J p t : ℕ) :
    Measurable (fun z : TransportAuxiliaryFrame.Store (Fintype.card (FrameIndex counts J))
      (auxiliaryCapacity counts J) D × Generators (n+1) D (size (n+1) p 1 1 t) =>
        hierarchyStoreData counts J p t z.1 z.2) := by
  apply Measurable.prodMk
  · exact ((measurable_pi_apply (Sum.inl ())).comp (auxiliaryStoreReadout_measurable counts J)).comp measurable_fst
  · apply Measurable.prodMk
    · apply measurable_pi_lambda
      intro j
      apply measurable_pi_lambda
      intro I
      by_cases hj : j<J
      · simp only [hierarchyOrdinaryReadout,dif_pos hj]
        exact ((measurable_pi_apply (Sum.inr (canonicalNode counts J ⟨j,Nat.lt_succ_of_lt hj⟩ I))).comp
          (auxiliaryStoreReadout_measurable counts J)).comp measurable_fst
      · simp only [hierarchyOrdinaryReadout,dif_neg hj]
        exact measurable_const
    · apply Measurable.prodMk <;> apply measurable_pi_lambda <;> intro j <;>
        apply measurable_pi_lambda <;> intro I
      · by_cases hj : j=J
        · subst j
          simp only [hierarchyEndpointReadout,dif_pos rfl]
          exact ((measurable_pi_apply I).comp (endpointReadout_measurable counts J p t 0)).comp measurable_snd
        · simp only [hierarchyEndpointReadout,dif_neg hj]
          exact measurable_const
      · by_cases hj : j=J
        · subst j
          simp only [hierarchyEndpointReadout,dif_pos rfl]
          exact ((measurable_pi_apply I).comp
            (endpointReadout_measurable counts J p t (Fin.last (n+1)))).comp measurable_snd
        · simp only [hierarchyEndpointReadout,dif_neg hj]
          exact measurable_const

theorem hierarchyOrdinaryReadout_unused {D : ℕ} (counts : ℕ → ℕ) (J : ℕ)
    (C : TransportAuxiliaryFrame.Store (Fintype.card (FrameIndex counts J)) (auxiliaryCapacity counts J) D)
    (j : ℕ) (I : List ℕ) (hj : J≤j) : hierarchyOrdinaryReadout counts J C j I=0 := by
  simp only [hierarchyOrdinaryReadout,dif_neg (by omega : ¬j<J)]

variable {H : Type*} {n D p : ℕ} (counts : ℕ → ℕ) (J : ℕ)
  (hdim : ∀ j,counts (j+1)+1≤D) (hT : capacity counts (J+1) 0≤D)
  (hAll : ∀ i : FrameIndex counts J,chainSize i+1≤D) (hA : auxiliaryCapacity counts J+1≤D)
  (s : PhysicalSample counts J n D)
  (choose : ∀ t,H × Generators (n+1) D (size (n+1) p 1 1 t) → Queries (n+1) D p)
  (respond : ∀ t,StepData H (n+1) D (size (n+1) p 1 1 t) p (capacity counts (J+1) 0) → H)
  (memory : H)

theorem hierarchyStoreData_prefix (t : ℕ) :
    let C := TransportAuxiliaryFrame.actualStore (auxiliaryRoundSchedule counts J (n+1) (Nat.succ_pos n)) t
      (fun a => TransportNetworkAuxiliary.auxiliaryFrame (auxiliaryCapacity counts J+1) hA a s)
    let g := (run (capacity counts (J+1) 0) hT choose respond (prefixNames (n+1) (capacity counts (J+1) 0))
      (memory,seed (capacity counts (J+1) 0) hT s.1) s.1 t).2
    let data := hierarchyStoreData counts J p t C g
    let q := t/(n+1)
    (∀ k : Fin (counts 0+1),k.val<counter counts (J+1) q 0 [] → data.1 k=physicalMacroFrame hAll s (basis k)) ∧
    (∀ j I,j<J → ∀ k : Fin (counts (j+1)+1),k.val<canonicalCounter counts J q j I →
      data.2.1 j I k=physicalFamily hdim hT s j I (basis k)) ∧
    (∀ I,∀ k : Fin (counts (J+1)+1),k.val<canonicalCounter counts J (q+1) J I →
      data.2.2.1 J I k=endpointFrame (physicalRotations s.1) (physicalFamily hdim hT s J I) 0 (basis k)) ∧
    (∀ I,∀ k : Fin (counts (J+1)+1),k.val<canonicalCounter counts J q J I →
      data.2.2.2 J I k=endpointFrame (physicalRotations s.1) (physicalFamily hdim hT s J I) (Fin.last (n+1)) (basis k)) := by
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · intro k hk
    exact auxiliaryStoreReadout_macro hAll hA (n+1) (Nat.succ_pos n) s t k hk
  · intro j I hj k hk
    change hierarchyOrdinaryReadout counts J _ j I k=_
    simp only [hierarchyOrdinaryReadout,dif_pos hj]
    exact auxiliaryStoreReadout_ancestor hdim hT hAll hA (n+1) (Nat.succ_pos n) s t j hj I k hk
  · intro I k hk
    change hierarchyEndpointReadout counts J p t _ 0 J I k=_
    simp only [hierarchyEndpointReadout,dif_pos rfl,physicalFamily_terminal]
    exact endpointSourceReadout_prefix counts J hT choose respond memory s.1 t I k hk
  · intro I k hk
    change hierarchyEndpointReadout counts J p t _ (Fin.last (n+1)) J I k=_
    simp only [hierarchyEndpointReadout,dif_pos rfl,physicalFamily_terminal]
    exact endpointTargetReadout_prefix counts J hT choose respond memory s.1 t I k hk

end Bilevel.TransportHierarchy
