import Bilevel.TransportHierarchyStoreData
import Bilevel.PrefixGramMeasurable

/-! Actual observable stores satisfy all required Gram identities, with
old macro/ancestor and separate next-source/old-target endpoint timing. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiHierarchyHaar TransportRound
  TransportNetwork EndpointTransportResponse ChiPrefixEvaluation
set_option maxHeartbeats 1200000

theorem gram_of_frame_prefix {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (U : Space n →ₗᵢ[ℝ] E) (r : ℕ) (C : Fin (n+1) → E)
    (h : ∀ k : Fin (n+1),k.val<r → C k=U (basis k)) : PrefixGram n r C := by
  intro i j hi hj
  rw [h i hi,h j hj,U.inner_map_map,inner_basis]
  simp only [basis,EuclideanSpace.single_apply,eq_comm]

variable {H : Type*} {n D p : ℕ} (counts : ℕ → ℕ) (J : ℕ)
  (hdim : ∀ j,counts (j+1)+1≤D) (hT : capacity counts (J+1) 0≤D)
  (hAll : ∀ i : FrameIndex counts J,chainSize i+1≤D) (hA : auxiliaryCapacity counts J+1≤D)
  (s : PhysicalSample counts J n D)
  (choose : ∀ t,H × Generators (n+1) D (size (n+1) p 1 1 t) → Queries (n+1) D p)
  (respond : ∀ t,StepData H (n+1) D (size (n+1) p 1 1 t) p (capacity counts (J+1) 0) → H)
  (memory : H)

include hdim hAll in
theorem hierarchyStoreData_gram (t : ℕ) :
    let C := TransportAuxiliaryFrame.actualStore (auxiliaryRoundSchedule counts J (n+1) (Nat.succ_pos n)) t
      (fun a => TransportNetworkAuxiliary.auxiliaryFrame (auxiliaryCapacity counts J+1) hA a s)
    let g := (run (capacity counts (J+1) 0) hT choose respond (prefixNames (n+1) (capacity counts (J+1) 0))
      (memory,seed (capacity counts (J+1) 0) hT s.1) s.1 t).2
    let data := hierarchyStoreData counts J p t C g
    let q := t/(n+1)
    PrefixGram (counts 0) (counter counts (J+1) q 0 []) data.1 ∧
    (∀ j I,j<J → PrefixGram (counts (j+1)) (canonicalCounter counts J q j I) (data.2.1 j I)) ∧
    (∀ I,PrefixGram (counts (J+1)) (canonicalCounter counts J (q+1) J I) (data.2.2.1 J I)) ∧
    (∀ I,PrefixGram (counts (J+1)) (canonicalCounter counts J q J I) (data.2.2.2 J I)) := by
  have hp := hierarchyStoreData_prefix counts J hdim hT hAll hA s choose respond memory t
  dsimp only at hp ⊢
  exact ⟨gram_of_frame_prefix (physicalMacroFrame hAll s) _ _ hp.1,
    fun j I hj => gram_of_frame_prefix (physicalFamily hdim hT s j I) _ _ (hp.2.1 j I hj),
    fun I => gram_of_frame_prefix (endpointFrame (physicalRotations s.1) (physicalFamily hdim hT s J I) 0) _ _ (hp.2.2.1 I),
    fun I => gram_of_frame_prefix (endpointFrame (physicalRotations s.1) (physicalFamily hdim hT s J I) (Fin.last (n+1))) _ _ (hp.2.2.2 I)⟩

end Bilevel.TransportHierarchy
