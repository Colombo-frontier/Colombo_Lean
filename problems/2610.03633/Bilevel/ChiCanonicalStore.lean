import Bilevel.ChiHierarchyStore
import Bilevel.ChiCanonicalFrameFamily

/-! Exact all-list prefix data for the same finite sampled hierarchy.
The canonical hidden frame and the finite disclosed store use the same
legal node, including on nonlegal natural-number/list indices. -/
noncomputable section
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiPrefixEvaluation

theorem actual_extended_prefix {counts : ℕ → ℕ} {J D : ℕ}
    (hD : ∀ j, counts (j+1)+1 ≤ D)
    (hAll : ∀ i : FrameIndex counts J, chainSize i+1 ≤ D)
    (a : Orientations counts J D) (q j : ℕ) (I : List ℕ) :
    extendColumns (actual counts J q (columns hAll a)).2 j I =
      paddedPrefix (counts (j+1)) (canonicalCounter counts J q j I)
        (fun k => canonicalFamily hD a j I (ChiBoundedChain.basis k)) := by
  by_cases hj : j ≤ J
  · let i : Node counts J := canonicalNode counts J ⟨j,by omega⟩ I
    simp only [extendColumns,canonicalCounter,dif_pos hj,actual]
    funext k
    unfold paddedPrefix
    split_ifs
    · change columns hAll a (Sum.inr i) k = canonicalFamily hD a j I (ChiBoundedChain.basis k)
      rw [canonicalFamily_covered hD hAll a j hj I]
      exact (frame_basis hAll a (Sum.inr i) k).symm
    · rfl
  · simp only [extendColumns,canonicalCounter,dif_neg hj]
    funext k
    simp [paddedPrefix]

theorem actual_macro_prefix {counts : ℕ → ℕ} {J D : ℕ}
    (hAll : ∀ i : FrameIndex counts J, chainSize i+1 ≤ D)
    (a : Orientations counts J D) (q : ℕ) :
    (actual counts J q (columns hAll a)).2 (Sum.inl ()) =
      paddedPrefix (counts 0) (ChiTreeProgress.counter counts (J+1) q 0 [])
        (fun k => frame hAll a (Sum.inl ()) (ChiBoundedChain.basis k)) := by
  funext k
  change (if k.val < retained counts J q (Sum.inl ()) then columns hAll a (Sum.inl ()) k else 0) = _
  simp only [paddedPrefix,retained,frame_basis]

end Bilevel.ChiHierarchyHaar
