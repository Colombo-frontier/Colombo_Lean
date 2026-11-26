import Bilevel.TransportAugmentedSharedSpace

/-! One analytical auxiliary space for the actual current round: all
retained columns and all current auxiliary query vectors. It is a subspace
of every selected-frame observer space; those larger spaces are not
identified with each other. -/
noncomputable section
open MeasureTheory
universe u v
namespace Bilevel.TransportAugmented
open EuclideanGaussian TransportRound TransportNetwork ProjectionGeometry
set_option autoImplicit false
set_option maxHeartbeats 700000
variable {C : Type u} {S : Type v} [MeasurableSpace C] [MeasurableSpace S]
  {n D p Tnet k T B : ℕ}

def analyticalAuxSpace (A : Controller C S n D p Tnet (k+1) T B) (t : ℕ)
    (s : CommonState C S (k+1) T D × Generators n D (size n p 1 1 t)) :
    Submodule ℝ (Space D) := sharedSpace s.1 ⊔ Submodule.span ℝ (Set.range (A.auxiliaryQueries t s))

theorem analyticalAuxSpace_retained (A : Controller C S n D p Tnet (k+1) T B) (t : ℕ)
    (s : CommonState C S (k+1) T D × Generators n D (size n p 1 1 t))
    (j : Fin (k+1)) (col : Fin (T+1)) : (s.1.2.2 j).2 col∈analyticalAuxSpace A t s :=
  Submodule.mem_sup_left (Submodule.subset_span ⟨(j,col),rfl⟩)

theorem analyticalAuxSpace_query (A : Controller C S n D p Tnet (k+1) T B) (t : ℕ)
    (s : CommonState C S (k+1) T D × Generators n D (size n p 1 1 t)) (b : Fin B) :
    A.auxiliaryQueries t s b∈analyticalAuxSpace A t s :=
  Submodule.mem_sup_right (Submodule.subset_span ⟨b,rfl⟩)

theorem analyticalAuxSpace_le_observer (P : TransportAuxiliaryFrame.Schedule (k+1) T)
    (A : Controller C S n D p Tnet (k+1) T B) (hTnet : Tnet≤D) (hT : T+1≤D)
    (i : Fin (k+1)) (hB : 0<(k+1)*(T+1)+B) (initial : C → S)
    (output : Fin (k+1) → CommonState C S (k+1) T D → Space D)
    (ho : ∀ i,Measurable (output i))
    (s : C × TransportNetworkAuxiliary.Sample n D (k+1)) (t : ℕ) :
    analyticalAuxSpace A t ((masterRun P A hTnet hT initial s t).1.2,
      (masterRun P A hTnet hT initial s t).2)≤
        enlargedPreSpace P A hTnet hT i hB initial output ho s t := by
  apply sup_le
  · exact sharedSpace_le_preSpace P A hTnet hT i hB initial output ho s t
  · apply Submodule.span_le.mpr
    rintro _ ⟨b,rfl⟩
    exact current_query_mem_preSpace P A hTnet hT i hB initial output ho s t b

theorem analyticalAuxSpace_energy (P : TransportAuxiliaryFrame.Schedule (k+1) T)
    (A : Controller C S n D p Tnet (k+1) T B) (hTnet : Tnet≤D) (hT : T+1≤D)
    (i : Fin (k+1)) (hB : 0<(k+1)*(T+1)+B) (initial : C → S)
    (output : Fin (k+1) → CommonState C S (k+1) T D → Space D)
    (ho : ∀ i,Measurable (output i)) (cap : ℝ)
    (s : C × TransportNetworkAuxiliary.Sample n D (k+1)) (N t : ℕ) (ht : t<N)
    (h : FrameObserved P (enlargeBatch A) hTnet hT hB initial N cap output ho i s) :
    GenieProtocol.BoundedEnergy
      (analyticalAuxSpace A t ((masterRun P A hTnet hT initial s t).1.2,
        (masterRun P A hTnet hT initial s t).2))
      (TransportAuxiliaryFrame.knownPrefix P t i) (TransportAuxiliaryFrame.originalColumns hT s.2 i) cap :=
  SourceFrameActions.boundedEnergy_subspace
    (analyticalAuxSpace_le_observer P A hTnet hT i hB initial output ho s t) _ _ cap
    (enlarged_query_energy P A hTnet hT i hB initial output ho cap s N t ht h)

theorem analyticalAuxSpace_projection (P : TransportAuxiliaryFrame.Schedule (k+1) T)
    (A : Controller C S n D p Tnet (k+1) T B) (hTnet : Tnet≤D) (hT : T+1≤D)
    (i : Fin (k+1)) (hB : 0<(k+1)*(T+1)+B) (initial : C → S)
    (output : Fin (k+1) → CommonState C S (k+1) T D → Space D)
    (ho : ∀ i,Measurable (output i)) (cap : ℝ)
    (s : C × TransportNetworkAuxiliary.Sample n D (k+1)) (N t : ℕ) (ht : t<N)
    (h : FrameObserved P (enlargeBatch A) hTnet hT hB initial N cap output ho i s)
    (col : Fin (T+1)) (hc : P.count t i≤col.val) :
    ‖(analyticalAuxSpace A t ((masterRun P A hTnet hT initial s t).1.2,
      (masterRun P A hTnet hT initial s t).2)).orthogonalProjection
        (TransportAuxiliaryFrame.originalColumns hT s.2 i col)‖≤Real.sqrt cap := by
  have hh := analyticalAuxSpace_energy P A hTnet hT i hB initial output ho cap s N t ht h col
    (show col∉TransportAuxiliaryFrame.knownPrefix P t i by exact not_lt.mpr hc)
  exact Real.le_sqrt_of_sq_le hh

end Bilevel.TransportAugmented
