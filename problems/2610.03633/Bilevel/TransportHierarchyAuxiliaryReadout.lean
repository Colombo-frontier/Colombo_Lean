import Bilevel.TransportHierarchyFamily
import Bilevel.TransportAuxiliaryFrameActual

/-! Literal macro/ancestor arrays extracted from the padded finite
auxiliary prefix store, with exact identities under the original joint
network+auxiliary prior. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiHierarchyHaar ChiBoundedChain EuclideanGaussian
  TransportAuxiliaryFrame
set_option maxHeartbeats 700000

def auxiliaryColumnIndex (counts : ℕ → ℕ) (J : ℕ) (i : FrameIndex counts J)
    (k : Fin (chainSize i+1)) : Fin (auxiliaryCapacity counts J+1) :=
  Fin.castLE (Nat.add_le_add_right (chainSize_le_auxiliaryCapacity counts J i) 1) k

def auxiliaryStoreReadout {D : ℕ} (counts : ℕ → ℕ) (J : ℕ)
    (C : Store (Fintype.card (FrameIndex counts J)) (auxiliaryCapacity counts J) D) :
    FiniteColumns counts J (EuclideanGaussian.Space D) :=
  fun i k => (C (enumerate counts J i)).2 (auxiliaryColumnIndex counts J i k)

theorem auxiliaryStoreReadout_measurable {D : ℕ} (counts : ℕ → ℕ) (J : ℕ) :
    Measurable (auxiliaryStoreReadout (D:=D) counts J) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro k
  exact (measurable_pi_apply (auxiliaryColumnIndex counts J i k)).comp
    (measurable_snd.comp (measurable_pi_apply (enumerate counts J i)))

theorem auxiliary_column_nested {counts : ℕ → ℕ} {J n D : ℕ}
    (hAll : ∀ i : FrameIndex counts J,chainSize i+1≤D)
    (hA : auxiliaryCapacity counts J+1≤D) (s : PhysicalSample counts J n D)
    (i : FrameIndex counts J) (k : Fin (chainSize i+1)) :
    TransportNetworkAuxiliary.auxiliaryFrame (auxiliaryCapacity counts J+1) hA
      (enumerate counts J i) s (auxiliaryColumnIndex counts J i k)=
        ChiHierarchyHaar.frame hAll (auxiliaryOrientations s) i (basis k) := by
  rw [ChiHierarchyHaar.frame_basis]
  unfold TransportNetworkAuxiliary.auxiliaryFrame ChiHierarchyHaar.columns HaarFrame.frame
    auxiliaryOrientations auxiliaryColumnIndex
  congr 2

theorem auxiliaryStoreReadout_actual {counts : ℕ → ℕ} {J n D : ℕ}
    (hAll : ∀ i : FrameIndex counts J,chainSize i+1≤D)
    (hA : auxiliaryCapacity counts J+1≤D) (length : ℕ) (hL : 0<length)
    (s : PhysicalSample counts J n D) (t : ℕ) (i : FrameIndex counts J) (k : Fin (chainSize i+1)) :
    auxiliaryStoreReadout counts J
      (TransportAuxiliaryFrame.actualStore (auxiliaryRoundSchedule counts J length hL) t
        (fun a => TransportNetworkAuxiliary.auxiliaryFrame (auxiliaryCapacity counts J+1) hA a s)) i k=
      if k.val<retained counts J (t/length) i then
        ChiHierarchyHaar.frame hAll (auxiliaryOrientations s) i (basis k) else 0 := by
  unfold auxiliaryStoreReadout TransportAuxiliaryFrame.actualStore ChiPrefixEvaluation.actualStore
    ChiPrefixEvaluation.paddedPrefix
  rw [auxiliaryRoundSchedule_count]
  change (if k.val<retained counts J (t/length) i then _ else 0)=_
  rw [auxiliary_column_nested hAll hA s i k]

theorem auxiliaryStoreReadout_macro {counts : ℕ → ℕ} {J n D : ℕ}
    (hAll : ∀ i : FrameIndex counts J,chainSize i+1≤D)
    (hA : auxiliaryCapacity counts J+1≤D) (length : ℕ) (hL : 0<length)
    (s : PhysicalSample counts J n D) (t : ℕ) (k : Fin (counts 0+1))
    (hk : k.val<counter counts (J+1) (t/length) 0 []) :
    auxiliaryStoreReadout counts J
      (TransportAuxiliaryFrame.actualStore (auxiliaryRoundSchedule counts J length hL) t
        (fun a => TransportNetworkAuxiliary.auxiliaryFrame (auxiliaryCapacity counts J+1) hA a s)) (Sum.inl ()) k=
      physicalMacroFrame hAll s (basis k) := by
  rw [auxiliaryStoreReadout_actual hAll hA length hL s t (Sum.inl ()) k]
  change (if k.val<counter counts (J+1) (t/length) 0 [] then _ else 0)=_
  rw [if_pos hk]
  rfl

theorem auxiliaryStoreReadout_ancestor {counts : ℕ → ℕ} {J n D : ℕ}
    (hdim : ∀ j,counts (j+1)+1≤D) (hT : capacity counts (J+1) 0≤D)
    (hAll : ∀ i : FrameIndex counts J,chainSize i+1≤D)
    (hA : auxiliaryCapacity counts J+1≤D) (length : ℕ) (hL : 0<length)
    (s : PhysicalSample counts J n D) (t j : ℕ) (hj : j<J) (I : List ℕ)
    (k : Fin (counts (j+1)+1)) (hk : k.val<canonicalCounter counts J (t/length) j I) :
    auxiliaryStoreReadout counts J
      (TransportAuxiliaryFrame.actualStore (auxiliaryRoundSchedule counts J length hL) t
        (fun a => TransportNetworkAuxiliary.auxiliaryFrame (auxiliaryCapacity counts J+1) hA a s))
        (Sum.inr (canonicalNode counts J ⟨j,Nat.lt_succ_of_lt hj⟩ I)) k=
      physicalFamily hdim hT s j I (basis k) := by
  let i : FrameIndex counts J := Sum.inr (canonicalNode counts J ⟨j,Nat.lt_succ_of_lt hj⟩ I)
  have hk' : k.val<retained counts J (t/length) i := by
    simpa only [canonicalCounter,dif_pos hj.le,i] using hk
  have hh := auxiliaryStoreReadout_actual hAll hA length hL s t i k
  rw [if_pos hk'] at hh
  exact hh.trans (congrArg (fun F => F (basis k))
    (physicalFamily_ancestor hdim hT hAll s j hj I)).symm

end Bilevel.TransportHierarchy
