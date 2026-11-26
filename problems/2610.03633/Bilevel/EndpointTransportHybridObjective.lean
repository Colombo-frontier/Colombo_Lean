import Bilevel.EndpointTransportHybridPrimitive
import Bilevel.EndpointTransportOuterTrace
import Bilevel.ChiOuterJoint

/-! Exact collapse of the physical hybrid response to the original recursive
objective. Only earlier ordinary blocks are read by the physical recursion;
the missing deepest ordinary block is supplied by the endpoint gain. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre ChiBoundedChain ChiRecursive ChiOuter ChiCarrier

theorem physicalRecursive_congr_before {n D : ℕ} (Q : Rotations n D) (G : Geometry (Block D))
    (d j : ℕ) (I : List ℕ) (u v : ℕ → Block D) (Y : Physical n D)
    (huv : ∀ k,j≤k → k<j+d → u k=v k) :
    physicalRecursive Q G d j I u Y=physicalRecursive Q G d j I v Y := by
  induction d generalizing j I with
  | zero => rfl
  | succ d ih =>
    have hj := huv j le_rfl (by omega)
    have hr (i : Fin ((G j I).n+1)) :
        (if d=0 then physicalRelease Q (G (j+1) (child I i.val)) Y
          else (G (j+1) (child I i.val)).release (u (j+1)))=
        (if d=0 then physicalRelease Q (G (j+1) (child I i.val)) Y
          else (G (j+1) (child I i.val)).release (v (j+1))) := by
      by_cases hd : d=0
      · rw [if_pos hd,if_pos hd]
      · rw [if_neg hd,if_neg hd,huv (j+1) (by omega) (by omega)]
    have hc (i : Fin ((G j I).n+1)) := ih (j+1) (child I i.val)
      (fun k hk ht => huv k (by omega) (by omega))
    simp only [physicalRecursive,hj,hr,hc]

theorem physicalPublic_congr_before {n D : ℕ} (ρ R : ℕ → ℝ) (d j : ℕ)
    (u v : ℕ → Block D) (Y : Physical n D)
    (huv : ∀ k,j≤k → k<j+d → u k=v k) :
    physicalPublic ρ R d j u Y=physicalPublic ρ R d j v Y := by
  induction d generalizing j with
  | zero => rfl
  | succ d ih =>
    simp only [physicalPublic,huv j le_rfl (by omega)]
    rw [ih (j+1) (fun k hk ht => huv k (by omega) (by omega))]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem physicalOuter_congr_before {n D : ℕ} (Q : Rotations n D) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (ρ R : ℕ → ℝ) (d : ℕ) (x : E)
    (u v : ℕ → Block D) (Y : Physical n D) (huv : ∀ k,k<d → u k=v k) :
    physicalOuter Q M ν G ρ R d x u Y=physicalOuter Q M ν G ρ R d x v Y := by
  have hr (i : Fin (M.n+1)) :
      (if d=0 then physicalRelease Q (G 0 [i.val]) Y else (G 0 [i.val]).release (u 0))=
      (if d=0 then physicalRelease Q (G 0 [i.val]) Y else (G 0 [i.val]).release (v 0)) := by
    by_cases hd : d=0
    · rw [if_pos hd,if_pos hd]
    · rw [if_neg hd,if_neg hd,huv 0 (by omega)]
  have hc (i : Fin (M.n+1)) := physicalRecursive_congr_before Q G d 0 [i.val] u v Y
    (fun k _ ht => huv k (by omega))
  have hp := physicalPublic_congr_before ρ R d 0 u v Y (fun k _ ht => huv k (by omega))
  simp only [physicalOuter,hr,hc,hp]

def sourceOuterCoordinates {D J : ℕ} (κ : ℝ) (x : HybridOuter E (Blocks J (Block D)) D) :
    ℕ → Block D := Function.update (padded (EndpointTransportNormalization.gain κ • x.fst.snd))
      J (EndpointTransportNormalization.gain κ • x.snd)

theorem source_physical_gain {L κ : ℝ} (hL : 0<L) (hκ : 3200≤κ) :
    gain (EndpointTransportNormalization.interiors κ) (L/16) (L/4)=EndpointTransportNormalization.gain κ := by
  rw [EndpointTransportNormalization.gain_eq_endpoint_ratio hL hκ,EndpointTransportMatrix.inverse_last_last]
  rfl

theorem source_physical_outer_response {D J : ℕ} {L κ : ℝ} (hL : 0<L) (hκ : 3200≤κ)
    (Q : Rotations (EndpointTransportNormalization.interiors κ) D) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (ρ R : ℕ → ℝ) (x : HybridOuter E (Blocks J (Block D)) D) :
    physicalOuter Q M ν G ρ R J x.fst.fst
        (padded (sourceHybridTangent L κ Q x).fst) (sourceHybridTangent L κ Q x).snd=
      outerObjective M ν G ρ R J x.fst.fst (sourceOuterCoordinates κ x) := by
  change physicalOuter Q M ν G ρ R J x.fst.fst
    (padded (EndpointTransportNormalization.gain κ • x.fst.snd)) (physicalResponse (L/16) (L/4) Q x.snd)=_
  rw [physicalOuter_congr_before Q M ν G ρ R J x.fst.fst _ (sourceOuterCoordinates κ x) _ (by
    intro k hk
    exact (Function.update_of_ne (by omega : k≠J) _ _).symm)]
  apply physical_outer_response (L/16) (L/4) Q M ν G ρ R J x.fst.fst (sourceOuterCoordinates κ x) x.snd
  rw [source_physical_gain hL hκ]
  exact Function.update_self _ _ _

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem source_hybrid_mean_identity {D J : ℕ} {L κ μ Lf Lg Cf ρg : ℝ}
    (hL : 0<L) (hκ : 3200≤κ)
    (Q : Rotations (EndpointTransportNormalization.interiors κ) D) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (ρ R : ℕ → ℝ)
    (P : Joint (HybridOuter E (Blocks J (Block D)) D)
      (HybridVariables (Blocks J (Block D)) V (EndpointTransportNormalization.interiors κ) D) → ℝ)
    (base : E → HybridTangent (Blocks J (Block D)) (EndpointTransportNormalization.interiors κ) D → ℝ)
    (b : V)
    (htrace : ∀ x p,base x.fst.fst p+⟪b,(gradient P (pack x (pack p (0:V)))).snd.snd⟫=
      physicalOuter Q M ν G ρ R J x.fst.fst (padded p.fst) p.snd)
    (Pr : Model.Primitive (X:=HybridOuter E (Blocks J (Block D)) D)
      (Y:=HybridVariables (Blocks J (Block D)) V (EndpointTransportNormalization.interiors κ) D) μ Lf Lg Cf ρg)
    (hf : ∀ x y,Pr.f x y=base x.fst.fst y.fst+⟪b,y.snd⟫)
    (r : Pr.Response) (hr : ∀ x,r.y x=ChiHybrid.responseOfExtension P (sourceHybridTangent L κ Q) x)
    (x : HybridOuter E (Blocks J (Block D)) D) :
    Pr.hyperobjective r x=outerObjective M ν G ρ R J x.fst.fst (sourceOuterCoordinates κ x) := by
  change Pr.f x (r.y x)=_
  rw [hr,hf]
  change base x.fst.fst (sourceHybridTangent L κ Q x)+
    ⟪b,(gradient P (pack x (pack (sourceHybridTangent L κ Q x) (0:V)))).snd.snd⟫=_
  rw [htrace]
  exact source_physical_outer_response hL hκ Q M ν G ρ R x

end Bilevel.EndpointTransportResponse
