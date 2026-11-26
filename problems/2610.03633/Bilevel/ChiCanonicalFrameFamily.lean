import Bilevel.ChiCanonicalHierarchy
import Bilevel.ChiHierarchyFrameFamily

/-! Covered total source frames: every list at an in-range level uses a
legal random frame, via exactly the canonicalization used by retained counts.
This closes the all-list versus finite-frame mismatch in blind certificates. -/
noncomputable section
open MeasureTheory
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex
set_option maxHeartbeats 700000

def canonicalOrientation {counts : ℕ → ℕ} {J D : ℕ} (a : Orientations counts J D)
    (j : ℕ) (I : List ℕ) : OrthogonalHaar.Group D :=
  if hj : j ≤ J then a (Sum.inr (canonicalNode counts J ⟨j,by omega⟩ I)) else 1

theorem canonicalOrientation_measurable {counts : ℕ → ℕ} {J D : ℕ} (j : ℕ) (I : List ℕ) :
    Measurable (fun a : Orientations counts J D => canonicalOrientation a j I) := by
  unfold canonicalOrientation
  split_ifs with hj
  · exact measurable_pi_apply _
  · exact measurable_const

def canonicalFamily {counts : ℕ → ℕ} {J D : ℕ}
    (hD : ∀ j, counts (j+1)+1 ≤ D) (a : Orientations counts J D) (j : ℕ) (I : List ℕ) :
    ChiBoundedChain.Space (counts (j+1)) →ₗᵢ[ℝ] EuclideanGaussian.Space D :=
  (OrthogonalAction.isometry D (canonicalOrientation a j I)).toLinearIsometry.comp
    (ChiPrefixEvaluation.auxiliaryFrame (counts (j+1)) D (hD j))

theorem canonicalFamily_covered {counts : ℕ → ℕ} {J D : ℕ}
    (hD : ∀ j, counts (j+1)+1 ≤ D)
    (hAll : ∀ i : FrameIndex counts J, chainSize i+1 ≤ D)
    (a : Orientations counts J D) (j : ℕ) (hj : j ≤ J) (I : List ℕ) :
    canonicalFamily hD a j I = frame hAll a (Sum.inr (canonicalNode counts J ⟨j,by omega⟩ I)) := by
  simp only [canonicalFamily,canonicalOrientation,dif_pos hj,frame,chainSize,canonicalNode]

theorem canonicalFamily_at_node {counts : ℕ → ℕ} {J D : ℕ}
    (hD : ∀ j, counts (j+1)+1 ≤ D)
    (hAll : ∀ i : FrameIndex counts J, chainSize i+1 ≤ D)
    (a : Orientations counts J D) (i : Node counts J) :
    canonicalFamily hD a i.1.val (nodeList i) = frame hAll a (Sum.inr i) := by
  rw [canonicalFamily_covered hD hAll a _ (Nat.le_of_lt_succ i.1.isLt)]
  change frame hAll a (Sum.inr ⟨i.1,canonicalPath counts (i.1.val+1) (toList i.2)⟩) = _
  rw [canonicalPath_toList]

theorem canonicalFamily_column_measurable {counts : ℕ → ℕ} {J D : ℕ}
    (hD : ∀ j, counts (j+1)+1 ≤ D) (j : ℕ) (I : List ℕ) (k : Fin (counts (j+1)+1)) :
    Measurable (fun a : Orientations counts J D => canonicalFamily hD a j I (ChiBoundedChain.basis k)) := by
  change Measurable (fun a : Orientations counts J D => canonicalOrientation a j I •
    ChiPrefixEvaluation.auxiliaryFrame (counts (j+1)) D (hD j) (ChiBoundedChain.basis k))
  exact (canonicalOrientation_measurable j I).smul measurable_const

theorem finite_column_property_all_lists {counts : ℕ → ℕ} {J D : ℕ}
    (hD : ∀ j, counts (j+1)+1 ≤ D)
    (hAll : ∀ i : FrameIndex counts J, chainSize i+1 ≤ D)
    (a : Orientations counts J D) (q : ℕ) (P : ℕ → ℕ → EuclideanGaussian.Space D → Prop)
    (hP : ∀ i : Node counts J, ∀ k : Fin (chainSize (Sum.inr i)+1),
      retained counts J q (Sum.inr i) ≤ k.val → P i.1.val k.val (columns hAll a (Sum.inr i) k))
    (j : ℕ) (hj : j ≤ J) (I : List ℕ) (k : Fin (counts (j+1)+1))
    (hk : canonicalCounter counts J q j I ≤ k.val) :
    P j k.val (canonicalFamily hD a j I (ChiBoundedChain.basis k)) := by
  let i : Node counts J := canonicalNode counts J ⟨j,by omega⟩ I
  have hr : canonicalCounter counts J q j I = retained counts J q (Sum.inr i) := dif_pos hj
  rw [hr] at hk
  rw [canonicalFamily_covered hD hAll a j hj I]
  change P j k.val (frame hAll a (Sum.inr i) (ChiBoundedChain.basis k))
  rw [frame_basis hAll a (Sum.inr i) k]
  exact hP i k hk

end Bilevel.ChiHierarchyHaar
