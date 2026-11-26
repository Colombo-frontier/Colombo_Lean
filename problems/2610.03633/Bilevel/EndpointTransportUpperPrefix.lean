import Bilevel.EndpointTransportVirtualParent
import Bilevel.EndpointTransportUpperBase
import Bilevel.ChiVirtualUpperValues

/-! Actual physical upper-base evaluation from OLD disclosed columns.
The macro chain and release correction are combined before truncation.
At depth one the last parent uses target releases, without source columns. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  PrimitiveGeometry PartialLegendre ChiPrefixEvaluation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def prefixPhysicalUpperBase {n D : ℕ} (m : ℕ) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (J : ℕ) (ρ R : ℝ) (rM : ℕ) (r : ℕ → List ℕ → ℕ)
    (macroColumns : Fin (M.n+1) → E) (columns : ∀ j I,Fin ((G j I).n+1) → Block D)
    (targetColumns : ∀ j I,Fin ((G j I).n+1) → Physical n D)
    (z : PhysicalBase E m n D) : ℝ :=
  virtualMacroValue M ν rM macroColumns z.fst+
    (virtualOuterReleaseCorrection m M G rM r macroColumns columns (baseOrdinaryCoordinates m n D z)+
      (∑ i : Fin (M.n+1),virtualOuterSelector M rM macroColumns i z.fst*
        virtualPhysicalCarrier G r r columns (fun _ _ _ => 0) targetColumns J 0 [i.val] 0 z.snd)+
      baseRadial m ρ R (baseOrdinaryCoordinates m n D z))

theorem physicalUpperCarrier_eq_prefix {m n D : ℕ} (Q : Rotations n D)
    (G : Geometry (Block D)) (J : ℕ) (hJ : 0<J)
    (r : ℕ → List ℕ → ℕ) (columns : ∀ k I,Fin ((G k I).n+1) → Block D)
    (T : ∀ k I,Fin ((G k I).n+1) → Physical n D)
    (hprefix : ∀ k A,∀ a : Fin ((G k A).n+1),a.val<r k A → columns k A a=(G k A).frame (basis a))
    (hh : ∀ A,0<(G 0 A).width)
    (hhp : ∀ A,0<(G 1 A).parentWidth) (hw : ∀ A,(G 1 A).width≤(G 1 A).parentWidth)
    (ht : ∀ A,∀ a : Fin ((G J A).n+1),a.val<r J A → T J A a=endpointFrame Q (G J A).frame (Fin.last (n+1)) (basis a))
    (x : HybridTangent (Blocks m (Block D)) n D)
    (hb : ∀ k A,k<J → ∀ a : Fin ((G k A).n+1),r k A≤a.val →
      |(G k A).coordinates (block m k x.fst) a|≤(G k A).width/4)
    (hbt : ∀ A,∀ a : Fin ((G J A).n+1),r J A≤a.val →
      |(physicalCoordinates Q (G J A) x.snd).snd a|≤(G J A).width/4)
    (hfuture : ∀ A,∀ i : Fin ((G 0 A).n+1),r 0 A ≤ i.val →
      r 1 (child A i.val)≤(G 1 (child A i.val)).n)
    (I : List ℕ) :
    physicalCarrier m Q G jointFstLinear jointSndLinear J 0 I 0 x=
      virtualPhysicalCarrier G r r columns (fun _ _ _ => 0) T J 0 I 0 x := by
  cases J with
  | zero => omega
  | succ d =>
    cases d with
    | zero =>
      have he := lastParentCarrier_eq_virtual Q 0 (G 0 I) (fun i => G 1 (child I i.val))
        (r 0 I) (fun i => r 1 (child I i.val)) (columns 0 I) (fun i => T 1 (child I i.val))
        (hprefix 0 I) (fun i => ht _) (hh I) (fun i => hhp _) (fun i => hw _) x
        (hb 0 I (by omega)) (fun i => hbt _) (hfuture I)
      simpa only [physicalCarrier,virtualPhysicalCarrier,if_pos rfl,if_true] using he
    | succ d =>
      simp only [physicalCarrier,virtualPhysicalCarrier,show ¬(d+1=0) by omega,if_false]
      apply actual_closedCarrier_eq_virtual G r columns (d+1) 0 I (padded x.fst) hprefix (hh I)
      · exact fun k A _ hk => hb k A (by omega)
      · exact hhp
      · exact hw
      · exact hfuture I

theorem physicalUpperBase_eq_prefix {m n D : ℕ} (Q : Rotations n D) (M : Node E)
    (ν : ℝ) (G : Geometry (Block D)) (J : ℕ) (hJ : 0<J) (ρ R : ℝ)
    (rM : ℕ) (r : ℕ → List ℕ → ℕ) (macroColumns : Fin (M.n+1) → E)
    (columns : ∀ k I,Fin ((G k I).n+1) → Block D)
    (T : ∀ k I,Fin ((G k I).n+1) → Physical n D)
    (hmp : ∀ a : Fin (M.n+1),a.val<rM → macroColumns a=M.frame (basis a))
    (hp : ∀ k A,∀ a : Fin ((G k A).n+1),a.val<r k A → columns k A a=(G k A).frame (basis a))
    (hmw : 0<M.width) (hh : ∀ A,0<(G 0 A).width)
    (hhp : ∀ k A,k≤1 → 0<(G k A).parentWidth)
    (hw : ∀ k A,k≤1 → (G k A).width≤(G k A).parentWidth)
    (ht : ∀ A,∀ a : Fin ((G J A).n+1),a.val<r J A → T J A a=endpointFrame Q (G J A).frame (Fin.last (n+1)) (basis a))
    (hmfuture : ∀ i : Fin (M.n+1),rM≤ i.val → r 0 [i.val]≤(G 0 [i.val]).n)
    (hfuture : ∀ A,∀ i : Fin ((G 0 A).n+1),r 0 A ≤ i.val →
      r 1 (child A i.val)≤(G 1 (child A i.val)).n)
    (z : PhysicalBase E m n D)
    (hmb : ∀ a : Fin (M.n+1),rM≤a.val → |M.coordinates z.fst a|≤M.width/4)
    (hb : ∀ k A,k<J → ∀ a : Fin ((G k A).n+1),r k A≤a.val →
      |(G k A).coordinates (block m k z.snd.fst) a|≤(G k A).width/4)
    (hbt : ∀ A,∀ a : Fin ((G J A).n+1),r J A≤a.val →
      |(physicalCoordinates Q (G J A) z.snd.snd).snd a|≤(G J A).width/4) :
    physicalUpperBase m Q M ν G J ρ R z=prefixPhysicalUpperBase m M ν G J ρ R rM r macroColumns columns T z := by
  have hm := actual_macro_release_eq_virtual m M ν G rM r macroColumns columns hmp (hp 0)
    hmw (fun A => hhp 0 A (by omega)) (fun A => hw 0 A (by omega)) hmfuture
    (baseOrdinaryCoordinates m n D z) hmb (fun A => hb 0 A hJ)
  have hc : outerPhysicalCarrier m Q M (baseMacroProjection m n D) G
      (baseOrdinaryProjection m n D) (basePhysicalProjection m n D) J 0 z=
      ∑ i : Fin (M.n+1),virtualOuterSelector M rM macroColumns i z.fst*
        virtualPhysicalCarrier G r r columns (fun _ _ _ => 0) T J 0 [i.val] 0 z.snd := by
    unfold outerPhysicalCarrier macroSelected
    apply Finset.sum_congr rfl
    intro i _
    change wrappedSelector M i z.fst*_=_
    rw [actual_outerSelector_eq_virtual M rM macroColumns hmp hmw i z.fst hmb]
    congr 1
    change physicalCarrier m Q G (baseOrdinaryProjection m n D) (basePhysicalProjection m n D) J 0 [i.val] 0 z=_
    rw [physicalCarrier_congr_inputs Q G (baseOrdinaryProjection (E:=E) m n D)
      (basePhysicalProjection (E:=E) m n D) jointFstLinear jointSndLinear z z.snd rfl rfl]
    exact physicalUpperCarrier_eq_prefix Q G J hJ r columns T hp hh
      (fun A => hhp 1 A le_rfl) (fun A => hw 1 A le_rfl) ht z.snd hb hbt hfuture [i.val]
  change macroValue M.n M.ell M.width ν M.radius M.frame z.fst+_=
    virtualMacroValue M ν rM macroColumns z.fst+_ at hm
  change macroValue M.n M.ell M.width ν M.radius M.frame z.fst+(_+_+_)=_+(_+_+_)
  linarith only [hm,hc]

end Bilevel.EndpointTransportResponse
