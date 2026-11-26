import Bilevel.ChiVirtualNodeValues
import Bilevel.ChiVirtualRecursion

/-! Exact recursive closed-carrier evaluation from disclosed prefixes.
Future child release vanishing is proved from the terminal blind bound. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem actual_closedCarrier_eq_virtual (D : Geometry E) (r : ℕ → List ℕ → ℕ)
    (columns : ∀ j I,Fin ((D j I).n+1) → E) (d j : ℕ) (I : List ℕ) (u : ℕ → E)
    (hprefix : ∀ k P,∀ a : Fin ((D k P).n+1),a.val<r k P → columns k P a=(D k P).frame (basis a))
    (hh : 0<(D j I).width)
    (hblind : ∀ k P,j≤k → k≤j+1 → ∀ a : Fin ((D k P).n+1),
      r k P≤a.val → |(D k P).coordinates (u k) a|≤(D k P).width/4)
    (hhp : ∀ P,0<(D (j+1) P).parentWidth)
    (hw : ∀ P,(D (j+1) P).width≤(D (j+1) P).parentWidth)
    (hfuture : ∀ i : Fin ((D j I).n+1),r j I ≤ i.val →
      r (j+1) (child I i.val)≤(D (j+1) (child I i.val)).n) :
    selectedCarrier D (d+1) j I 0 u=virtualCarrier D r columns (d+1) j I 0 u := by
  let q : Fin ((D j I).n+1) → ℝ := fun i => (D (j+1) (child I i.val)).release (u (j+1))
  have hq : ∀ i,r j I ≤ i.val → q i=0 := by
    intro i hi
    exact ((D (j+1) (child I i.val)).release_flat_of_blind_terminal
      (hhp _) (hw _) (u (j+1)) (hblind (j+1) _ (by omega) le_rfl
        (Fin.last _) (hfuture i hi))).1
  have he := actual_closed_eq_virtual (D j I) (r j I) (columns j I) (hprefix j I) hh q hq
    (u j) (hblind j I le_rfl (by omega))
  change (D j I).closed q (u j)=_ 
  rw [he]
  unfold virtualClosed virtualCarrier
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact actual_release_eq_virtual (D (j+1) (child I i.val)) (r (j+1) (child I i.val))
    (columns (j+1) (child I i.val)) (hprefix _ _) (hhp _) (hw _) (u (j+1))
    (hblind (j+1) _ (by omega) le_rfl)

theorem actual_selectedClosed_eq_virtual (D : Geometry E) (r : ℕ → List ℕ → ℕ)
    (columns : ∀ j I,Fin ((D j I).n+1) → E) (d t j : ℕ) (I : List ℕ) (u : ℕ → E)
    (hprefix : ∀ k P,∀ a : Fin ((D k P).n+1),a.val<r k P → columns k P a=(D k P).frame (basis a))
    (hh : ∀ k P,j≤k → k≤j+t → 0<(D k P).width)
    (hblind : ∀ k P,j≤k → k≤j+t+1 → ∀ a : Fin ((D k P).n+1),
      r k P≤a.val → |(D k P).coordinates (u k) a|≤(D k P).width/4)
    (hhp : ∀ P,0<(D (j+t+1) P).parentWidth)
    (hw : ∀ P,(D (j+t+1) P).width≤(D (j+t+1) P).parentWidth)
    (hfuture : ∀ P,∀ i : Fin ((D (j+t) P).n+1),r (j+t) P ≤ i.val →
      r (j+t+1) (child P i.val)≤(D (j+t+1) (child P i.val)).n) :
    selectedCarrier D (d+1+t) j I t u=virtualCarrier D r columns (d+1+t) j I t u := by
  induction t generalizing j I with
  | zero =>
    exact actual_closedCarrier_eq_virtual D r columns d j I u hprefix (hh j I le_rfl le_rfl)
      hblind hhp hw (hfuture I)
  | succ t ih =>
    change (∑ i : Fin ((D j I).n+1),(D j I).selector i (u j)*selectedCarrier D (d+1+t) (j+1) (child I i.val) t u)=
      ∑ i : Fin ((D j I).n+1),virtualSelector (D j I) (r j I) (columns j I) i (u j)*
        virtualCarrier D r columns (d+1+t) (j+1) (child I i.val) t u
    apply Finset.sum_congr rfl
    intro i _
    rw [actual_selector_eq_virtual (D j I) (r j I) (columns j I) (hprefix j I)
      (hh j I le_rfl (by omega)) i (u j) (hblind j I le_rfl (by omega))]
    congr 1
    apply ih (j+1) (child I i.val)
    · intro k P hk hkt
      exact hh k P (by omega) (by omega)
    · intro k P hk hkt
      exact hblind k P (by omega) (by omega)
    · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hhp
    · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hw
    · convert hfuture using 1
      rw [show j+1+t=j+(t+1) by omega]

end Bilevel.ChiPrefixEvaluation
