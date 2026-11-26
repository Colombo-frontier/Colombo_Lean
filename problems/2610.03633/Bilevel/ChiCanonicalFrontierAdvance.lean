import Bilevel.ChiSourceFrontierAdvance
import Bilevel.ChiCanonicalHierarchy

/-! Active frontier advance for the canonical all-list counter used by the
actual finite store. Legal recursion agrees with the raw sequential budget. -/
noncomputable section
namespace Bilevel.ChiHierarchyIndex
open ChiTreeProgress ChiRecursive ChiCarrier

theorem canonicalCounter_legal (counts : ℕ → ℕ) (J q j : ℕ) (I : List ℕ)
    (hj : j≤J) (hI : Legal counts I) (hlen : I.length=j+1) :
    canonicalCounter counts J q j I=innerCounter counts J q j I := by
  obtain ⟨i,hi,hlist⟩ := node_complete hj I hI hlen
  rw [←hi,←hlist,canonicalCounter_at_node]

theorem canonicalCounter_success_bounds (counts : ℕ → ℕ) (J q j : ℕ) (I : List ℕ) :
    canonicalCounter counts J q j I≤canonicalCounter counts J (q+1) j I ∧
      canonicalCounter counts J (q+1) j I≤canonicalCounter counts J q j I+1 := by
  by_cases hj : j≤J
  · simpa only [canonicalCounter,dif_pos hj] using retained_success_bounds counts J q
      (Sum.inr (canonicalNode counts J ⟨j,by omega⟩ I))
  · simp only [canonicalCounter,dif_neg hj]
    omega

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem frontierAdvance_canonical (D : Geometry E) (counts : ℕ → ℕ)
    (hsize : ∀ j I,(D j I).n=counts (j+1)) (J q : ℕ) :
    ∀ d j I, d+j≤J → Legal counts I → I.length=j+1 →
    FrontierAdvance D (innerCounter counts J q) (innerCounter counts J (q+1)) d j I →
      FrontierAdvance D (canonicalCounter counts J q) (canonicalCounter counts J (q+1)) d j I := by
  intro d
  induction d with
  | zero =>
    intro j I hj hI hlen h
    change (D j I).n<canonicalCounter counts J q j I ∨
      canonicalCounter counts J q j I<canonicalCounter counts J (q+1) j I
    rw [canonicalCounter_legal counts J q j I (by omega) hI hlen,
      canonicalCounter_legal counts J (q+1) j I (by omega) hI hlen]
    exact h
  | succ d ih =>
    intro j I hj hI hlen h i hi
    have hi' : i.val ≤ innerCounter counts J q j I := by
      rwa [canonicalCounter_legal counts J q j I (by omega) hI hlen] at hi
    have hk : i.val<counts I.length+1 := by rw [hlen,←hsize j I];exact i.isLt
    have hc : Legal counts (child I i.val) := legal_child hI ⟨i.val,hk⟩
    exact ih (j+1) (child I i.val) (by omega) hc
      (by simp only [child,List.length_append,List.length_singleton,hlen]) (h i hi')

theorem canonical_frontierAdvance (D : Geometry E) (counts : ℕ → ℕ)
    (hsize : ∀ j I,(D j I).n=counts (j+1)) (J q : ℕ) (i : Fin (counts 0+1))
    (hi : i.val≤counter counts (J+1) q 0 []) :
    FrontierAdvance D (canonicalCounter counts J q) (canonicalCounter counts J (q+1)) J 0 [i.val] :=
  frontierAdvance_canonical D counts hsize J q J 0 [i.val] (by omega)
    (legal_macro counts i) rfl (inner_frontierAdvance D counts hsize J q i hi)

end Bilevel.ChiHierarchyIndex
