import Bilevel.EndpointTransportVirtualLeaves
import Bilevel.ChiFrontierAdvance

/-! Actual physical leaf selection from ordinary disclosed prefixes. The
fine comparison requires a prospective source column only along reachable
branches; future selectors vanish before their leaves are examined. -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier
  PrimitiveGeometry PartialLegendre ChiPrefixEvaluation ChiTreeProgress

theorem liftedSelect_eq_virtual {m n D : ℕ} (G : Geometry (Block D))
    (r : ℕ → List ℕ → ℕ) (columns : ∀ k I,Fin ((G k I).n+1) → Block D)
    (f g : ℕ → List ℕ → Physical n D → ℝ) (d j : ℕ) (I : List ℕ)
    (x : HybridTangent (Blocks m (Block D)) n D)
    (hprefix : ∀ k A,j≤k → k<j+d → ∀ a : Fin ((G k A).n+1),a.val<r k A →
      columns k A a=(G k A).frame (basis a))
    (hh : ∀ k A,j≤k → k<j+d → 0<(G k A).width)
    (hb : ∀ k A,j≤k → k<j+d → ∀ a : Fin ((G k A).n+1),r k A≤a.val →
      |(G k A).coordinates (block m k x.fst) a|≤(G k A).width/4)
    (hleaf : ∀ A,f (j+d) A x.snd=g (j+d) A x.snd) :
    ChiLiftedCarrier.selectFamily m G jointFstLinear (fun k A y => f k A (jointSndLinear y)) d j I x=
      virtualPhysicalSelect G r columns g d j I x := by
  induction d generalizing j I with
  | zero => exact hleaf I
  | succ d ih =>
    change (∑ i : Fin ((G j I).n+1),(G j I).selector i (block m j x.fst)*
      ChiLiftedCarrier.selectFamily m G jointFstLinear (fun k A y => f k A (jointSndLinear y)) d (j+1) (child I i.val) x)=_
    rw [virtualPhysicalSelect]
    apply Finset.sum_congr rfl
    intro i _
    rw [actual_selector_eq_virtual (G j I) (r j I) (columns j I) (hprefix j I le_rfl (by omega))
      (hh j I le_rfl (by omega)) i (block m j x.fst) (hb j I le_rfl (by omega))]
    congr 1
    apply ih (j+1) (child I i.val)
    · exact fun k A hk hkd => hprefix k A (by omega) (by omega)
    · exact fun k A hk hkd => hh k A (by omega) (by omega)
    · exact fun k A hk hkd => hb k A (by omega) (by omega)
    · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hleaf

theorem selectedFine_eq_virtual_reachable {m n D : ℕ} (Q : Rotations n D)
    (G : Geometry (Block D)) (P : ChiFine.Parameters) (r sourceCount : ℕ → List ℕ → ℕ)
    (columns : ∀ k I,Fin ((G k I).n+1) → Block D)
    (S T : ∀ k I,Fin ((G k I).n+1) → Physical n D)
    (p d j : ℕ) (I : List ℕ) (x : HybridTangent (Blocks m (Block D)) n D)
    (hprefix : ∀ k A,j≤k → k<j+d → ∀ a : Fin ((G k A).n+1),a.val<r k A → columns k A a=(G k A).frame (basis a))
    (hh : ∀ k A,j≤k → k<j+d → 0<(G k A).width)
    (hb : ∀ k A,j≤k → k<j+d → ∀ a : Fin ((G k A).n+1),r k A≤a.val →
      |(G k A).coordinates (block m k x.fst) a|≤(G k A).width/4)
    (hrs : ∀ A,r (j+d) A≤sourceCount (j+d) A)
    (hs : ∀ A,∀ a : Fin ((G (j+d) A).n+1),a.val<sourceCount (j+d) A →
      S (j+d) A a=endpointFrame Q (G (j+d) A).frame 0 (basis a))
    (ht : ∀ A,∀ a : Fin ((G (j+d) A).n+1),a.val<r (j+d) A →
      T (j+d) A a=endpointFrame Q (G (j+d) A).frame (Fin.last (n+1)) (basis a))
    (hbt : ∀ A,∀ a : Fin ((G (j+d) A).n+1),r (j+d) A≤a.val →
      |(physicalCoordinates Q (G (j+d) A) x.snd).snd a|≤3*P.β/16)
    (hfront : FrontierAdvance G r sourceCount d j I) :
    selectedPhysicalFinePiece m G jointFstLinear jointSndLinear Q P p d j I x=
      virtualPhysicalFinePiece G P r sourceCount columns S T p d j I x := by
  induction d generalizing j I with
  | zero =>
    apply physicalFinePiece_eq_prefixAt Q (G j I) P p (r j I) (sourceCount j I) (hrs I) _
      (S j I) (T j I) (hs I) (ht I) x.snd (hbt I)
    intro hj
    change (G j I).n<r j I ∨ r j I<sourceCount j I at hfront
    omega
  | succ d ih =>
    change (∑ i : Fin ((G j I).n+1),(G j I).selector i (block m j x.fst)*
      selectedPhysicalFinePiece m G jointFstLinear jointSndLinear Q P p d (j+1) (child I i.val) x)=_
    change _=∑ i : Fin ((G j I).n+1),virtualSelector (G j I) (r j I) (columns j I) i (block m j x.fst)*
      virtualPhysicalFinePiece G P r sourceCount columns S T p d (j+1) (child I i.val) x
    apply Finset.sum_congr rfl
    intro i _
    have he := actual_selector_eq_virtual (G j I) (r j I) (columns j I)
      (hprefix j I le_rfl (by omega)) (hh j I le_rfl (by omega)) i (block m j x.fst) (hb j I le_rfl (by omega))
    by_cases hi : i.val≤r j I
    · rw [he]
      congr 1
      apply ih (j+1) (child I i.val)
      · exact fun k A hk hkd => hprefix k A (by omega) (by omega)
      · exact fun k A hk hkd => hh k A (by omega) (by omega)
      · exact fun k A hk hkd => hb k A (by omega) (by omega)
      · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hrs
      · rw [show j+1+d=j+(d+1) by omega]
        exact hs
      · rw [show j+1+d=j+(d+1) by omega]
        exact ht
      · rw [show j+1+d=j+(d+1) by omega]
        exact hbt
      · exact hfront i hi
    · have hz : (G j I).selector i (block m j x.fst)=0 := by
        apply ChiCarrier.selector_future_zero (r j I) _ _ i (by omega)
        intro k hk
        exact ZeroChainResidualScaled.scaled_coordinate_small _ (hh j I le_rfl (by omega)) _ k
          (hb j I le_rfl (by omega) k hk)
      rw [← he,hz,zero_mul,zero_mul]

end Bilevel.EndpointTransportResponse
