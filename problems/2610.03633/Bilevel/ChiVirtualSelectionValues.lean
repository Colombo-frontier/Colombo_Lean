import Bilevel.ChiVirtualClosedValues
import Bilevel.ChiVirtualFine

/-! Pointwise original-to-disclosed evaluation of selected leaves and the
deepest centered carrier. Actual selector and receiver cancellation inputs
are supplied by the concrete node identities. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem actual_select_eq_virtual (m : ℕ) (D : Geometry E) (r : ℕ → List ℕ → ℕ)
    (columns : ∀ j I,Fin ((D j I).n+1) → E) (leaf : ∀ j I,Space (D j I).n → ℝ)
    (d j : ℕ) (I : List ℕ) (x : Blocks m E)
    (hprefix : ∀ k P,∀ a : Fin ((D k P).n+1),a.val<r k P → columns k P a=(D k P).frame (basis a))
    (hh : ∀ k P,j≤k → k<j+d → 0<(D k P).width)
    (hblind : ∀ k P,j≤k → k<j+d → ∀ a : Fin ((D k P).n+1),
      r k P≤a.val → |(D k P).coordinates (block m k x) a|≤(D k P).width/4)
    (hleaf : ∀ P,leaf (j+d) P ((D (j+d) P).coordinates (block m (j+d) x))=
      leaf (j+d) P (readout (D (j+d) P).n (r (j+d) P) (D (j+d) P).radius
        (columns (j+d) P) (block m (j+d) x))) :
    selectFamily m D (fun k P y => leaf k P ((D k P).coordinates (block m k y))) d j I x=
      virtualSelect D r columns leaf d j I (padded x) := by
  induction d generalizing j I with
  | zero => exact hleaf I
  | succ d ih =>
    dsimp only [selectFamily,virtualSelect]
    apply Finset.sum_congr rfl
    intro i _
    change (D j I).selector i (block m j x)*_=virtualSelector (D j I) (r j I) (columns j I) i (block m j x)*_
    rw [actual_selector_eq_virtual (D j I) (r j I) (columns j I) (hprefix j I)
      (hh j I le_rfl (by omega)) i (block m j x) (hblind j I le_rfl (by omega))]
    congr 1
    apply ih (j+1) (child I i.val)
    · intro k P hk hkd
      exact hh k P (by omega) (by omega)
    · intro k P hk hkd
      exact hblind k P (by omega) (by omega)
    · convert hleaf using 1
      rw [show j+1+d=j+(d+1) by omega]

def centeredLeaf (D : Geometry E) (j : ℕ) (I : List ℕ) (z : Space (D j I).n) : ℝ :=
  payload (D j I).n (D j I).ell (D j I).width (D j I).receiver (D j I).nu
      (D j I).force (D j I).parentWidth (D j I).tailRadius z-
    (D j I).H 0-ChiFine.frontier (D j I).n (D j I).ell (D j I).width z

theorem centeredLeaf_eq_virtual (D : Geometry E) (r : ℕ → List ℕ → ℕ)
    (columns : ∀ j I,Fin ((D j I).n+1) → E) (j : ℕ) (I : List ℕ) (u : E)
    (hprefix : ∀ a : Fin ((D j I).n+1),a.val<r j I → columns j I a=(D j I).frame (basis a))
    (hh : 0<(D j I).width)
    (hz : ∀ a : Fin ((D j I).n+1),r j I≤a.val → |(D j I).coordinates u a|≤(D j I).width/4) :
    centeredLeaf D j I ((D j I).coordinates u)=
      centeredLeaf D j I (readout (D j I).n (r j I) (D j I).radius (columns j I) u) := by
  have he := actual_centered_eq_virtual (D j I) (r j I) (columns j I) hprefix hh u hz
  unfold centeredLeaf
  change (D j I).H u-(D j I).H 0-ChiFine.frontier (D j I).n (D j I).ell (D j I).width ((D j I).coordinates u)=
    virtualH (D j I) (r j I) (columns j I) u-(D j I).H 0-
      ChiFine.frontier (D j I).n (D j I).ell (D j I).width (readout (D j I).n (r j I) (D j I).radius (columns j I) u)
  linarith

theorem virtual_deepest_eq_select (D : Geometry E) (r : ℕ → List ℕ → ℕ)
    (columns : ∀ j I,Fin ((D j I).n+1) → E) (d j : ℕ) (I : List ℕ) (u : ℕ → E) :
    virtualCarrier D r columns d j I d u-virtualSelect D r columns (frontierLeaf D) d j I u=
      virtualSelect D r columns (centeredLeaf D) d j I u := by
  induction d generalizing j I with
  | zero =>
    dsimp only [virtualCarrier,virtualSelect,frontierLeaf,centeredLeaf]
    rw [← actual_zero_eq_virtual]
    rfl
  | succ d ih =>
    simp only [virtualCarrier,virtualSelect,← Finset.sum_sub_distrib,← mul_sub,ih]

theorem actual_deepest_eq_virtual (m : ℕ) (D : Geometry E) (r : ℕ → List ℕ → ℕ)
    (columns : ∀ j I,Fin ((D j I).n+1) → E) (d j : ℕ) (I : List ℕ) (x : Blocks m E)
    (hprefix : ∀ k P,∀ a : Fin ((D k P).n+1),a.val<r k P → columns k P a=(D k P).frame (basis a))
    (hh : ∀ k P,j≤k → k≤j+d → 0<(D k P).width)
    (hblind : ∀ k P,j≤k → k≤j+d → ∀ a : Fin ((D k P).n+1),
      r k P≤a.val → |(D k P).coordinates (block m k x) a|≤(D k P).width/4) :
    deepestCarrier m D d j I x=
      virtualCarrier D r columns d j I d (padded x)-
        virtualSelect D r columns (frontierLeaf D) d j I (padded x) := by
  rw [virtual_deepest_eq_select,deepestCarrier_eq_selected]
  exact actual_select_eq_virtual m D r columns (centeredLeaf D) d j I x hprefix
    (fun k P hk hkd => hh k P hk (by omega))
    (fun k P hk hkd => hblind k P hk (by omega))
    (fun P => centeredLeaf_eq_virtual D r columns (j+d) P (block m (j+d) x)
      (hprefix _ _) (hh _ _ (by omega) le_rfl) (hblind _ _ (by omega) le_rfl))

end Bilevel.ChiPrefixEvaluation
