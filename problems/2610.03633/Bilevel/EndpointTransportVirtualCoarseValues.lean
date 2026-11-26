import Bilevel.EndpointTransportVirtualParent
import Bilevel.EndpointTransportVirtualCoarseRecursion

/-! Exact old-prefix evaluation of every actual physical coarse carrier.
The last parent uses closed-carrier cancellation; the deepest leaf uses
centered split-payload cancellation. No extra source column is assumed. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier
  PrimitiveGeometry PartialLegendre ChiPrefixEvaluation

theorem physicalCoarse_eq_virtual {m n D : ℕ} (Q : Rotations n D)
    (G : Geometry (Block D)) (P : ChiFine.Parameters) (J : ℕ)
    (r sourceCount : ℕ → List ℕ → ℕ) (columns : ∀ k I,Fin ((G k I).n+1) → Block D)
    (S T : ∀ k I,Fin ((G k I).n+1) → Physical n D)
    (hprefix : ∀ k A,∀ a : Fin ((G k A).n+1),a.val<r k A → columns k A a=(G k A).frame (basis a))
    (hh : ∀ k A,k≤J → 0<(G k A).width)
    (hhp : ∀ k A,k≤J → 0<(G k A).parentWidth)
    (hw : ∀ k A,k≤J → (G k A).width≤(G k A).parentWidth)
    (hℓ : ∀ A,P.ℓ=(G J A).ell) (hβ : ∀ A,P.β=(G J A).width)
    (hrs : ∀ A,r J A≤sourceCount J A)
    (hs : ∀ A,∀ a : Fin ((G J A).n+1),a.val<sourceCount J A → S J A a=endpointFrame Q (G J A).frame 0 (basis a))
    (ht : ∀ A,∀ a : Fin ((G J A).n+1),a.val<r J A → T J A a=endpointFrame Q (G J A).frame (Fin.last (n+1)) (basis a))
    (x : HybridTangent (Blocks m (Block D)) n D)
    (hb : ∀ k A,k<J → ∀ a : Fin ((G k A).n+1),r k A≤a.val →
      |(G k A).coordinates (block m k x.fst) a|≤(G k A).width/4)
    (hbt : ∀ A,∀ a : Fin ((G J A).n+1),r J A≤a.val →
      |(physicalCoordinates Q (G J A) x.snd).snd a|≤3*(G J A).width/16)
    (hfuture : ∀ k,k<J → ∀ A,∀ i : Fin ((G k A).n+1),r k A ≤ i.val →
      r (k+1) (child A i.val)≤(G (k+1) (child A i.val)).n)
    (d j t : ℕ) (I : List ℕ) (htd : t≤d) (hdepth : j+d=J) :
    physicalCoarseCarrier m Q G jointFstLinear jointSndLinear P d j I t x=
      virtualPhysicalCoarseCarrier G P r sourceCount columns S T d j I t x := by
  induction d generalizing j I t with
  | zero =>
    have ht0 : t=0 := by omega
    subst t
    have hj : j=J := by omega
    subst j
    have he := physicalCentered_eq_prefixAt Q (G J I) P (hℓ I) (hβ I) (r J I) (sourceCount J I)
      (hrs I) (S J I) (T J I) (hs I) (ht I) (hh J I le_rfl) x.snd (hbt I)
    change physicalPayload Q (G J I) x.snd-(G J I).H 0-physicalFineFrontier Q (G J I) P x.snd=
      prefixPhysicalPayloadAt (G J I) (sourceCount J I) (r J I) (S J I) (T J I) x.snd-
        physicalNodeOrigin (G J I)-ChiSplitFine.frontier (G J I).n P.ℓ P.β
          (prefixPhysicalCoordinatesAt (G J I) (sourceCount J I) (r J I) (S J I) (T J I) x.snd)
    rw [physicalNodeOrigin_eq]
    linarith only [he]
  | succ d ih =>
    cases t with
    | zero =>
      have hfun : 0≠d+1 := by omega
      simp only [physicalCoarseCarrier,virtualPhysicalCoarseCarrier,if_neg hfun,sub_zero]
      cases d with
      | zero =>
        have ht' : ∀ A,∀ a : Fin ((G (j+1) A).n+1),a.val<r (j+1) A →
            T (j+1) A a=endpointFrame Q (G (j+1) A).frame (Fin.last (n+1)) (basis a) := by
          rw [hdepth]
          exact ht
        have hb' : ∀ A,∀ a : Fin ((G (j+1) A).n+1),r (j+1) A≤a.val →
            |(physicalCoordinates Q (G (j+1) A) x.snd).snd a|≤(G (j+1) A).width/4 := by
          rw [hdepth]
          intro A a ha
          have h := hbt A a ha
          have hp := hh J A le_rfl
          linarith
        have he := lastParentCarrier_eq_virtual Q j (G j I) (fun i => G (j+1) (child I i.val))
          (r j I) (fun i => r (j+1) (child I i.val)) (columns j I) (fun i => T (j+1) (child I i.val))
          (hprefix j I) (fun i => ht' _) (hh j I (by omega))
          (fun i => hhp (j+1) _ (by omega)) (fun i => hw (j+1) _ (by omega)) x
          (hb j I (by omega)) (fun i => hb' _) (hfuture j (by omega) I)
        simpa only [physicalCarrier,virtualPhysicalCarrier,if_pos rfl,if_true] using he
      | succ d =>
        simp only [physicalCarrier,virtualPhysicalCarrier,show ¬(d+1=0) by omega,if_false]
        apply actual_closedCarrier_eq_virtual G r columns (d+1) j I (padded x.fst) hprefix (hh j I (by omega))
        · exact fun k A _ hk => hb k A (by omega)
        · exact fun A => hhp (j+1) A (by omega)
        · exact fun A => hw (j+1) A (by omega)
        · exact hfuture j (by omega) I
    | succ t =>
      rw [physicalCoarseCarrier_succ,virtualPhysicalCoarseCarrier_succ]
      apply Finset.sum_congr rfl
      intro i _
      rw [actual_selector_eq_virtual (G j I) (r j I) (columns j I) (hprefix j I)
        (hh j I (by omega)) i (block m j x.fst) (hb j I (by omega))]
      congr 1
      exact ih (j+1) t (child I i.val) (by omega) (by omega)

end Bilevel.EndpointTransportResponse
