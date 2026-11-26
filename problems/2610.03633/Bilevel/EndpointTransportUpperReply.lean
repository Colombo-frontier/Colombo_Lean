import Bilevel.EndpointTransportUpperGerm

/-! Actual arbitrary-query full upper-gradient equality for the physical
hierarchy, including the exact normal readout and spectator coordinates. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  PrimitiveGeometry PartialLegendre ChiPrefixEvaluation ChiExtension
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem physicalUpper_gradient_eq_prefix {n D s : ℕ} (Q : Rotations n D) (M : Node E)
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
    (b : Normals s)
    (q : Joint (HybridOuter E (Blocks J (Block D)) D)
      (HybridVariables (Blocks J (Block D)) (Normals s) n D))
    (hmb : ∀ a : Fin (M.n+1),rM≤a.val → |M.coordinates (pack q.fst.fst.fst q.snd.fst).fst a|≤M.width/8)
    (hb : ∀ k A,k<J → ∀ a : Fin ((G k A).n+1),r k A≤a.val →
      |(G k A).coordinates (block J k (pack q.fst.fst.fst q.snd.fst).snd.fst) a|≤(G k A).width/8)
    (hbt : ∀ A,∀ a : Fin ((G J A).n+1),r J A≤a.val →
      |(physicalCoordinates Q (G J A) (pack q.fst.fst.fst q.snd.fst).snd.snd).snd a|≤(G J A).width/8)
    (hmR : 0<M.radius) (hR : ∀ k A,k≤J → 0<(G k A).radius)
    (δ : ℝ) (hδ : 0<δ) (hδM : δ≤M.width/16) (hδG : ∀ k A,k≤J → δ≤(G k A).width/16) :
    gradient (physicalUpper (U:=Blocks J (Block D)) (D:=D)
      (physicalUpperBase J Q M ν G J ρ R) b) q=
    gradient (physicalUpper (U:=Blocks J (Block D)) (D:=D)
      (prefixPhysicalUpperBase J M ν G J ρ R rM r macroColumns columns T) b) q := by
  apply physicalUpper_gradient_eq_of_base_germ b q
  exact physicalUpperBase_eventuallyEq_prefix Q M ν G J hJ ρ R rM r macroColumns columns T
    hmp hp hmw hh hhp hw ht hmfuture hfuture (pack q.fst.fst.fst q.snd.fst) hmb hb hbt
    hmR hR δ hδ hδM hδG

end Bilevel.EndpointTransportResponse
