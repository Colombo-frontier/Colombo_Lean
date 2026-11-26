import Bilevel.EndpointTransportVirtualValues
import Bilevel.EndpointTransportUpperPrefix

/-! Complete arrays represent the original physical hierarchy globally.
These full arrays are used only for Borel dependence of the instance family,
never as information supplied to an adaptive algorithm. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  PrimitiveGeometry PartialLegendre ChiPrefixEvaluation ChiTreeProgress ChiExtension
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem full_frontierAdvance {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (G : Geometry F) (d j : ℕ) (I : List ℕ) :
    FrontierAdvance G (fun k A => (G k A).n+1) (fun k A => (G k A).n+1) d j I := by
  induction d generalizing j I with
  | zero => exact Or.inl (Nat.lt_succ_self _)
  | succ d ih => exact fun i _ => ih (j+1) (child I i.val)

theorem physicalHierarchyExtension_full_prefix {J n D s : ℕ} (Q : Rotations n D)
    (M : Node E) (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (ci ri : Fin J → Fin s) (fi : Fin s) (ρ R : ℕ → ℝ) (dn : ℝ)
    (MC : Fin (M.n+1) → E) (C : ∀ k I,Fin ((G k I).n+1) → Block D)
    (S T : ∀ k I,Fin ((G k I).n+1) → Physical n D)
    (hm : ∀ a,MC a=M.frame (basis a)) (hc : ∀ k I a,C k I a=(G k I).frame (basis a))
    (hs : ∀ I a,S J I a=endpointFrame Q (G J I).frame 0 (basis a))
    (ht : ∀ I a,T J I a=endpointFrame Q (G J I).frame (Fin.last (n+1)) (basis a))
    (hmw : 0<M.width) (hh : ∀ k A,k≤J → 0<(G k A).width)
    (hhp : ∀ k A,k≤J → 0<(G k A).parentWidth)
    (hw : ∀ k A,k≤J → (G k A).width≤(G k A).parentWidth)
    (hℓ : ∀ A,P.ℓ=(G J A).ell) (hβ : ∀ A,P.β=(G J A).width) :
    physicalHierarchyExtension Q M G P J s ci ri fi ρ R dn=
      prefixPhysicalHierarchyExtension M G P ci ri fi ρ R dn (M.n+1)
        (fun k A => (G k A).n+1) (fun k A => (G k A).n+1) MC C S T := by
  funext z
  refine physicalHierarchyExtension_eq_prefix Q M G P ci ri fi ρ R dn (M.n+1)
    (fun k A => (G k A).n+1) (fun k A => (G k A).n+1) MC C S T
    (fun a _ => hm a) (fun k I a _ => hc k I a) hmw hh hhp hw hℓ hβ
    (fun _ => le_rfl) (fun I a _ => hs I a) (fun I a _ => ht I a) ?_
    (fun i _ => full_frontierAdvance G J 0 [i.val]) z ?_ ?_ ?_
  · intro k _ I i hi
    exact False.elim ((Nat.not_le_of_lt i.isLt) hi)
  · intro a ha
    exact False.elim ((Nat.not_le_of_lt a.isLt) ha)
  · intro k I _ a ha
    exact False.elim ((Nat.not_le_of_lt a.isLt) ha)
  · intro I a ha
    exact False.elim ((Nat.not_le_of_lt a.isLt) ha)

theorem physicalUpperBase_full_prefix {m n D : ℕ} (Q : Rotations n D) (M : Node E)
    (ν : ℝ) (G : Geometry (Block D)) (J : ℕ) (hJ : 0<J) (ρ R : ℝ)
    (MC : Fin (M.n+1) → E) (C : ∀ k I,Fin ((G k I).n+1) → Block D)
    (T : ∀ k I,Fin ((G k I).n+1) → Physical n D)
    (hm : ∀ a,MC a=M.frame (basis a)) (hc : ∀ k I a,C k I a=(G k I).frame (basis a))
    (ht : ∀ I a,T J I a=endpointFrame Q (G J I).frame (Fin.last (n+1)) (basis a))
    (hmw : 0<M.width) (hh : ∀ I,0<(G 0 I).width)
    (hhp : ∀ k I,k≤1 → 0<(G k I).parentWidth)
    (hw : ∀ k I,k≤1 → (G k I).width≤(G k I).parentWidth) :
    physicalUpperBase m Q M ν G J ρ R=
      prefixPhysicalUpperBase m M ν G J ρ R (M.n+1) (fun k I => (G k I).n+1) MC C T := by
  funext z
  apply physicalUpperBase_eq_prefix Q M ν G J hJ ρ R (M.n+1) (fun k I => (G k I).n+1) MC C T
    (fun a _ => hm a) (fun k I a _ => hc k I a) hmw hh hhp hw (fun I a _ => ht I a)
  · intro i hi
    exact False.elim ((Nat.not_le_of_lt i.isLt) hi)
  · intro I i hi
    exact False.elim ((Nat.not_le_of_lt i.isLt) hi)
  · intro a ha
    exact False.elim ((Nat.not_le_of_lt a.isLt) ha)
  · intro k I _ a ha
    exact False.elim ((Nat.not_le_of_lt a.isLt) ha)
  · intro I a ha
    exact False.elim ((Nat.not_le_of_lt a.isLt) ha)

end Bilevel.EndpointTransportResponse
