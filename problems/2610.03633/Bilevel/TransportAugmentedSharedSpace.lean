import Bilevel.TransportAugmentedFrameOutputs

/-! The analytical shared auxiliary known space is contained in EVERY
selected-frame pre-reveal observer space. All retained columns and the
current query batch are inserted; terminal coordinates may differ by
frame. The actual master run is unchanged by these observer enlargements. -/
noncomputable section
open MeasureTheory
universe u v
namespace Bilevel.TransportAugmented
open EuclideanGaussian TransportNetwork TransportRound
set_option autoImplicit false
set_option maxHeartbeats 800000
variable {C : Type u} {S : Type v} [MeasurableSpace C] [MeasurableSpace S]
  {n D p Tnet k T B : ℕ}

def sharedSpace (s : CommonState C S (k+1) T D) : Submodule ℝ (Space D) :=
  Submodule.span ℝ (Set.range (fun a : Fin (k+1) × Fin (T+1) => (s.2.2 a.1).2 a.2))

def enlargedPreSpace (P : TransportAuxiliaryFrame.Schedule (k+1) T)
    (A : Controller C S n D p Tnet (k+1) T B) (hTnet : Tnet ≤ D) (hT : T+1 ≤ D)
    (i : Fin (k+1)) (hB : 0 < (k+1)*(T+1)+B) (initial : C → S)
    (output : Fin (k+1) → CommonState C S (k+1) T D → Space D)
    (ho : ∀ i,Measurable (output i))
    (s : C × TransportNetworkAuxiliary.Sample n D (k+1)) (M : ℕ) : Submodule ℝ (Space D) :=
  TransportAuxiliaryFrame.preSpace P
    (auxiliaryDriver (withAuxiliaryOutput (enlargeBatch A) (output i) (ho i)) hTnet (prefixNames n Tnet)) i hB M
    (TransportAuxiliaryFrame.otherColumns hT i (fun l => s.2.2 (i.succAbove l)))
    (TransportAuxiliaryFrame.originalColumns hT s.2)
    (TransportAuxiliaryFrame.originalInitial (auxiliaryInitial hTnet initial) s)

theorem retained_column_mem_preSpace (P : TransportAuxiliaryFrame.Schedule (k+1) T)
    (A : Controller C S n D p Tnet (k+1) T B) (hTnet : Tnet ≤ D) (hT : T+1 ≤ D)
    (i : Fin (k+1)) (hB : 0 < (k+1)*(T+1)+B) (initial : C → S)
    (output : Fin (k+1) → CommonState C S (k+1) T D → Space D)
    (ho : ∀ i,Measurable (output i))
    (s : C × TransportNetworkAuxiliary.Sample n D (k+1)) (M : ℕ) (j : Fin (k+1)) (col : Fin (T+1)) :
    (((masterRun P A hTnet hT initial s M).1.2.2.2 j).2 col) ∈
      enlargedPreSpace P A hTnet hT i hB initial output ho s M := by
  let st := ((masterRun P A hTnet hT initial s M).1.2,(masterRun P A hTnet hT initial s M).2)
  obtain ⟨b,hb⟩ := retained_mem_enlarged A M st j col
  have h := master_auxiliary_query_mem P (withAuxiliaryOutput (enlargeBatch A) (output i) (ho i))
    hTnet hT i hB initial s M b
  change (enlargeBatch A).auxiliaryQueries M st b ∈ enlargedPreSpace P A hTnet hT i hB initial output ho s M at h
  rw [hb] at h
  exact h

theorem sharedSpace_le_preSpace (P : TransportAuxiliaryFrame.Schedule (k+1) T)
    (A : Controller C S n D p Tnet (k+1) T B) (hTnet : Tnet ≤ D) (hT : T+1 ≤ D)
    (i : Fin (k+1)) (hB : 0 < (k+1)*(T+1)+B) (initial : C → S)
    (output : Fin (k+1) → CommonState C S (k+1) T D → Space D)
    (ho : ∀ i,Measurable (output i))
    (s : C × TransportNetworkAuxiliary.Sample n D (k+1)) (M : ℕ) :
    sharedSpace (masterRun P A hTnet hT initial s M).1.2 ≤
      enlargedPreSpace P A hTnet hT i hB initial output ho s M := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a,rfl⟩
  exact retained_column_mem_preSpace P A hTnet hT i hB initial output ho s M a.1 a.2

theorem current_query_mem_preSpace (P : TransportAuxiliaryFrame.Schedule (k+1) T)
    (A : Controller C S n D p Tnet (k+1) T B) (hTnet : Tnet ≤ D) (hT : T+1 ≤ D)
    (i : Fin (k+1)) (hB : 0 < (k+1)*(T+1)+B) (initial : C → S)
    (output : Fin (k+1) → CommonState C S (k+1) T D → Space D)
    (ho : ∀ i,Measurable (output i))
    (s : C × TransportNetworkAuxiliary.Sample n D (k+1)) (M : ℕ) (b : Fin B) :
    A.auxiliaryQueries M ((masterRun P A hTnet hT initial s M).1.2,
      (masterRun P A hTnet hT initial s M).2) b ∈
      enlargedPreSpace P A hTnet hT i hB initial output ho s M := by
  let st := ((masterRun P A hTnet hT initial s M).1.2,(masterRun P A hTnet hT initial s M).2)
  obtain ⟨a,ha⟩ := query_mem_enlarged A M st b
  have h := master_auxiliary_query_mem P (withAuxiliaryOutput (enlargeBatch A) (output i) (ho i))
    hTnet hT i hB initial s M a
  change (enlargeBatch A).auxiliaryQueries M st a ∈ enlargedPreSpace P A hTnet hT i hB initial output ho s M at h
  rw [ha] at h
  exact h

theorem enlarged_query_energy (P : TransportAuxiliaryFrame.Schedule (k+1) T)
    (A : Controller C S n D p Tnet (k+1) T B) (hTnet : Tnet ≤ D) (hT : T+1 ≤ D)
    (i : Fin (k+1)) (hB : 0 < (k+1)*(T+1)+B) (initial : C → S)
    (output : Fin (k+1) → CommonState C S (k+1) T D → Space D)
    (ho : ∀ i,Measurable (output i)) (cap : ℝ)
    (s : C × TransportNetworkAuxiliary.Sample n D (k+1)) (N j : ℕ) (hj : j < N)
    (h : FrameObserved P (enlargeBatch A) hTnet hT hB initial N cap output ho i s) :
    GenieProtocol.BoundedEnergy (enlargedPreSpace P A hTnet hT i hB initial output ho s j)
      (TransportAuxiliaryFrame.knownPrefix P j i) (TransportAuxiliaryFrame.originalColumns hT s.2 i) cap := by
  have hh := TransportAuxiliaryFrame.originalObserved_projectionGood P
    (auxiliaryDriver (withAuxiliaryOutput (enlargeBatch A) (output i) (ho i)) hTnet (prefixNames n Tnet))
    hT i hB N (auxiliaryInitial hTnet initial) cap s h
  exact hh.1 j hj

end Bilevel.TransportAugmented
