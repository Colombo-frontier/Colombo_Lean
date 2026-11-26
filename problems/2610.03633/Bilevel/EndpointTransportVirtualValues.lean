import Bilevel.EndpointTransportVirtualCoarseValues
import Bilevel.EndpointTransportVirtualSelection
import Bilevel.ChiVirtualOuterFineValues

/-! Exact complete physical hierarchy evaluation from the disclosed stores.
The source prefix advances only on reachable terminal branches; target and
ordinary prefix counts remain old. All normals are arbitrary. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  PrimitiveGeometry PartialLegendre ChiPrefixEvaluation ChiTreeProgress ChiExtension
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem physicalHierarchyExtension_eq_prefix {J n D s : ℕ} (Q : Rotations n D)
    (M : Node E) (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (coarseIndex radialIndex : Fin J → Fin s) (fineIndex : Fin s) (ρ R : ℕ → ℝ) (dn : ℝ)
    (rM : ℕ) (r sourceCount : ℕ → List ℕ → ℕ) (macroColumns : Fin (M.n+1) → E)
    (columns : ∀ k I,Fin ((G k I).n+1) → Block D)
    (S T : ∀ k I,Fin ((G k I).n+1) → Physical n D)
    (hm : ∀ a : Fin (M.n+1),a.val<rM → macroColumns a=M.frame (basis a))
    (hprefix : ∀ k A,∀ a : Fin ((G k A).n+1),a.val<r k A → columns k A a=(G k A).frame (basis a))
    (hmw : 0<M.width) (hh : ∀ k A,k≤J → 0<(G k A).width)
    (hhp : ∀ k A,k≤J → 0<(G k A).parentWidth)
    (hw : ∀ k A,k≤J → (G k A).width≤(G k A).parentWidth)
    (hℓ : ∀ A,P.ℓ=(G J A).ell) (hβ : ∀ A,P.β=(G J A).width)
    (hrs : ∀ A,r J A≤sourceCount J A)
    (hs : ∀ A,∀ a : Fin ((G J A).n+1),a.val<sourceCount J A → S J A a=endpointFrame Q (G J A).frame 0 (basis a))
    (ht : ∀ A,∀ a : Fin ((G J A).n+1),a.val<r J A → T J A a=endpointFrame Q (G J A).frame (Fin.last (n+1)) (basis a))
    (hfuture : ∀ k,k<J → ∀ A,∀ i : Fin ((G k A).n+1),r k A ≤ i.val →
      r (k+1) (child A i.val)≤(G (k+1) (child A i.val)).n)
    (hfront : ∀ i : Fin (M.n+1),i.val≤rM → FrontierAdvance G r sourceCount J 0 [i.val])
    (z : Full (PhysicalBase E J n D) s)
    (hmb : ∀ a : Fin (M.n+1),rM≤a.val → |M.coordinates z.fst.fst a|≤M.width/4)
    (hb : ∀ k A,k<J → ∀ a : Fin ((G k A).n+1),r k A≤a.val →
      |(G k A).coordinates (block J k z.fst.snd.fst) a|≤(G k A).width/4)
    (hbt : ∀ A,∀ a : Fin ((G J A).n+1),r J A≤a.val →
      |(physicalCoordinates Q (G J A) z.fst.snd.snd).snd a|≤3*(G J A).width/16) :
    physicalHierarchyExtension Q M G P J s coarseIndex radialIndex fineIndex ρ R dn z=
      prefixPhysicalHierarchyExtension M G P coarseIndex radialIndex fineIndex ρ R dn
        rM r sourceCount macroColumns columns S T z := by
  have hmacro (i : Fin (M.n+1)) := actual_outerSelector_eq_virtual M rM macroColumns hm hmw i z.fst.fst hmb
  have hcoarse (i : Fin J) : physicalHierarchyCoarse Q M G P J i z.fst=
      prefixPhysicalOuterCoarse M G P rM r sourceCount macroColumns columns S T i z.fst := by
    rw [show z.fst=pack z.fst.fst z.fst.snd from rfl,physicalHierarchyCoarse_slice]
    unfold prefixPhysicalOuterCoarse
    apply Finset.sum_congr rfl
    intro l _
    rw [hmacro l,physicalCoarse_eq_virtual Q G P J r sourceCount columns S T hprefix hh hhp hw hℓ hβ hrs hs ht
      z.fst.snd hb hbt hfuture J 0 (i.val+1) [l.val] (by omega) (by omega)]
    rfl
  have hfine (p : ℕ) : (physicalHierarchyFine Q M G P J).e p z.fst=
      prefixPhysicalOuterFinePiece M G P rM r sourceCount macroColumns columns S T p z.fst := by
    rw [show z.fst=pack z.fst.fst z.fst.snd from rfl,physicalHierarchyFine_piece_slice]
    unfold prefixPhysicalOuterFinePiece
    apply Finset.sum_congr rfl
    intro l _
    change wrappedSelector M l z.fst.fst *
      selectedPhysicalFinePiece J G jointFstLinear jointSndLinear Q P p J 0 [l.val] z.fst.snd=
      virtualOuterSelector M rM macroColumns l z.fst.fst *
        virtualPhysicalFinePiece G P r sourceCount columns S T p J 0 [l.val] z.fst.snd
    by_cases hl : l.val≤rM
    · rw [hmacro l]
      congr 1
      apply selectedFine_eq_virtual_reachable Q G P r sourceCount columns S T p J 0 [l.val] z.fst.snd
        (fun k A _ _ => hprefix k A) (fun k A _ hk => hh k A (by omega))
        (fun k A _ hk => hb k A (by omega))
        (by rw [Nat.zero_add]; exact hrs) (by rw [Nat.zero_add]; exact hs)
        (by rw [Nat.zero_add]; exact ht) _ (hfront l hl)
      rw [Nat.zero_add]
      intro A a ha
      rw [hβ A]
      exact hbt A a ha
    · have hz : wrappedSelector M l z.fst.fst=0 := by
        apply outer_selector_future_zero M.n rM _ _ l (by omega)
        intro a ha
        exact ZeroChainResidualScaled.scaled_coordinate_small _ hmw _ a (hmb a ha)
      rw [← hmacro l,hz,zero_mul,zero_mul]
  have hc : coarseSum coarseIndex (physicalHierarchyCoarse Q M G P J) (fun i => coarseWidth G (i.val+1)) z=
      ∑ i : Fin J,prefixPhysicalOuterCoarse M G P rM r sourceCount macroColumns columns S T i z.fst*
        SmallGapProfiles.normal (coarseWidth G (i.val+1)) (z.snd (coarseIndex i)) := by
    unfold coarseSum
    apply Finset.sum_congr rfl
    intro i _
    rw [show z=pack z.fst z.snd from rfl,normalTerm_formula,hcoarse]
    rfl
  have he : fineTerm s fineIndex (physicalHierarchyFine Q M G P J) z=
      ∑ p ∈ Finset.range (ZeroChainSchedule.levels P.θ+1),
        prefixPhysicalOuterFinePiece M G P rM r sourceCount macroColumns columns S T p z.fst*
          SmallGapProfiles.normal (ZeroChainSchedule.width P.c P.β P.θ p) (z.snd fineIndex) := by
    rw [fineTerm_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [show z=pack z.fst z.snd from rfl,normalTerm_formula,hfine]
    rfl
  change (1/dn)*(coarseSum coarseIndex (physicalHierarchyCoarse Q M G P J) _ z+
    fineTerm s fineIndex (physicalHierarchyFine Q M G P J) z)+_=_
  rw [hc,he]
  rfl

end Bilevel.EndpointTransportResponse
