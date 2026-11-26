import Bilevel.EndpointTransportCompletionNodes
import Bilevel.EndpointTransportVirtualFormula

/-! Cross-dimension scalar restriction of actual physical carriers. Only
actual ordinary and endpoint coordinate equalities are hypotheses; source
and target prefix counts remain independent. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre ChiBoundedChain ChiRecursive ChiCarrier ChiPrefixEvaluation
set_option autoImplicit false
set_option maxHeartbeats 1400000

section Nodes
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem nodeWithFrame_H_of_coordinates (N : Node E) (V : Space N.n →ₗᵢ[ℝ] F)
    (r : ℕ) (columns : Fin (N.n+1) → E) (x : E) (y : F)
    (h : (nodeWithFrame N V).coordinates y=readout N.n r N.radius columns x) :
    (nodeWithFrame N V).H y=virtualH N r columns x := by
  change payload N.n N.ell N.width N.receiver N.nu N.force N.parentWidth N.tailRadius
    ((nodeWithFrame N V).coordinates y)=_
  rw [h]
  rfl

theorem nodeWithFrame_selector_of_coordinates (N : Node E) (V : Space N.n →ₗᵢ[ℝ] F)
    (r : ℕ) (columns : Fin (N.n+1) → E) (x : E) (y : F)
    (h : (nodeWithFrame N V).coordinates y=readout N.n r N.radius columns x) (i : Fin (N.n+1)) :
    (nodeWithFrame N V).selector i y=virtualSelector N r columns i x := by
  change selector N.n i (N.width⁻¹ • (nodeWithFrame N V).coordinates y)=_
  rw [h]
  rfl

theorem nodeWithFrame_residual_of_coordinates (N : Node E) (V : Space N.n →ₗᵢ[ℝ] F)
    (r : ℕ) (columns : Fin (N.n+1) → E) (x : E) (y : F)
    (h : (nodeWithFrame N V).coordinates y=readout N.n r N.radius columns x) (i : Fin (N.n+1)) :
    (nodeWithFrame N V).residual i y=virtualResidual N r columns i x := by
  change ChiBoundedChain.Rterm N.n N.ell N.width i ((nodeWithFrame N V).coordinates y)=_
  rw [h]
  rfl

theorem nodeWithFrame_release_of_coordinates (N : Node E) (V : Space N.n →ₗᵢ[ℝ] F)
    (r : ℕ) (columns : Fin (N.n+1) → E) (x : E) (y : F)
    (h : (nodeWithFrame N V).coordinates y=readout N.n r N.radius columns x) :
    (nodeWithFrame N V).release y=virtualRelease N r columns x := by
  change releaseGate ((nodeWithFrame N V).coordinates y (Fin.last N.n)/N.parentWidth)=_
  rw [h]
  rfl
end Nodes

theorem nodeWithFrame_physicalPayload_of_coordinates {n D D' : ℕ}
    (Q : Rotations n D') (N : Node (Block D)) (V : Space N.n →ₗᵢ[ℝ] Block D')
    (rs rt : ℕ) (sourceColumns targetColumns : Fin (N.n+1) → Physical n D)
    (x : Physical n D) (y : Physical n D')
    (h : physicalCoordinates Q (nodeWithFrame N V) y=
      prefixPhysicalCoordinatesAt N rs rt sourceColumns targetColumns x) :
    physicalPayload Q (nodeWithFrame N V) y=prefixPhysicalPayloadAt N rs rt sourceColumns targetColumns x := by
  change ChiSplitChain.payload N.n N.ell N.width N.receiver N.nu N.force N.parentWidth N.tailRadius
    (physicalCoordinates Q (nodeWithFrame N V) y)=_
  rw [h]
  rfl

theorem nodeWithFrame_physicalRelease_of_coordinates {n D D' : ℕ}
    (Q : Rotations n D') (N : Node (Block D)) (V : Space N.n →ₗᵢ[ℝ] Block D')
    (rs rt : ℕ) (sourceColumns targetColumns : Fin (N.n+1) → Physical n D)
    (x : Physical n D) (y : Physical n D')
    (h : physicalCoordinates Q (nodeWithFrame N V) y=
      prefixPhysicalCoordinatesAt N rs rt sourceColumns targetColumns x) :
    physicalRelease Q (nodeWithFrame N V) y=prefixPhysicalRelease N rt targetColumns x := by
  change releaseGate ((physicalCoordinates Q (nodeWithFrame N V) y).snd (Fin.last N.n)/N.parentWidth)=_
  rw [h]
  rfl

theorem rebuilt_physicalCarrier_eq_virtual {m n D D' : ℕ}
    (G : Geometry (Block D)) (V : ∀ j I,Space (G j I).n →ₗᵢ[ℝ] Block D') (Q : Rotations n D')
    (J : ℕ) (r sourceCount : ℕ → List ℕ → ℕ)
    (columns : ∀ j I,Fin ((G j I).n+1) → Block D)
    (sourceColumns targetColumns : ∀ j I,Fin ((G j I).n+1) → Physical n D)
    (x : HybridTangent (Blocks m (Block D)) n D) (y : HybridTangent (Blocks m (Block D')) n D')
    (hc : ∀ j I,j<J → (geometryWithFrames G V j I).coordinates (block m j y.fst)=
      readout (G j I).n (r j I) (G j I).radius (columns j I) (block m j x.fst))
    (hp : ∀ I,physicalCoordinates Q (geometryWithFrames G V J I) y.snd=
      prefixPhysicalCoordinatesAt (G J I) (sourceCount J I) (r J I) (sourceColumns J I) (targetColumns J I) x.snd)
    (d j : ℕ) (I : List ℕ) (t : ℕ) (hd : j+d=J) :
    physicalCarrier m Q (geometryWithFrames G V)
      (jointFstLinear (A:=Blocks m (Block D')) (B:=Physical n D'))
      (jointSndLinear (A:=Blocks m (Block D')) (B:=Physical n D')) d j I t y=
      virtualPhysicalCarrier G r sourceCount columns sourceColumns targetColumns d j I t x := by
  have hyF : jointFstLinear (A:=Blocks m (Block D')) (B:=Physical n D') y=y.fst := rfl
  have hyS : jointSndLinear (A:=Blocks m (Block D')) (B:=Physical n D') y=y.snd := rfl
  have hH (k : ℕ) (A : List ℕ) (hk : k<J) :
      (geometryWithFrames G V k A).H (block m k y.fst)=virtualH (G k A) (r k A) (columns k A) (block m k x.fst) :=
    nodeWithFrame_H_of_coordinates (G k A) (V k A) (r k A) (columns k A) (block m k x.fst) (block m k y.fst) (hc k A hk)
  have hs (k : ℕ) (A : List ℕ) (hk : k<J) (i : Fin ((G k A).n+1)) :
      (geometryWithFrames G V k A).selector i (block m k y.fst)=virtualSelector (G k A) (r k A) (columns k A) i (block m k x.fst) :=
    nodeWithFrame_selector_of_coordinates (G k A) (V k A) (r k A) (columns k A) (block m k x.fst) (block m k y.fst) (hc k A hk) i
  have hr (k : ℕ) (A : List ℕ) (hk : k<J) (i : Fin ((G k A).n+1)) :
      (geometryWithFrames G V k A).residual i (block m k y.fst)=virtualResidual (G k A) (r k A) (columns k A) i (block m k x.fst) :=
    nodeWithFrame_residual_of_coordinates (G k A) (V k A) (r k A) (columns k A) (block m k x.fst) (block m k y.fst) (hc k A hk) i
  have hl (k : ℕ) (A : List ℕ) (hk : k<J) :
      (geometryWithFrames G V k A).release (block m k y.fst)=virtualRelease (G k A) (r k A) (columns k A) (block m k x.fst) :=
    nodeWithFrame_release_of_coordinates (G k A) (V k A) (r k A) (columns k A) (block m k x.fst) (block m k y.fst) (hc k A hk)
  induction d generalizing j I t with
  | zero =>
    have hj : j=J := by omega
    subst j
    cases t with
    | zero =>
      change physicalPayload Q (nodeWithFrame (G J I) (V J I)) y.snd-
        (nodeWithFrame (G J I) (V J I)).H 0=_
      rw [nodeWithFrame_physicalPayload_of_coordinates Q (G J I) (V J I) _ _ _ _ _ _ (hp I)]
      simp only [Node.H,Node.coordinates_zero,nodeWithFrame,virtualPhysicalCarrier,physicalNodeOrigin]
    | succ t => rfl
  | succ d ih =>
    have hj : j<J := by omega
    cases t with
    | zero =>
      by_cases hd0 : d=0
      · subst d
        have hjJ : j+1=J := by omega
        simp only [physicalCarrier,virtualPhysicalCarrier,if_pos rfl,if_true,lastParentCarrier,
          physicalReleaseCorrection,jointH,jointResidual,Function.comp_apply,hyF,hyS]
        rw [hH j I hj]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [hr j I hj i]
        congr 2
        have hp' := hp (child I i.val)
        rw [←hjJ] at hp'
        exact nodeWithFrame_physicalRelease_of_coordinates Q (G (j+1) (child I i.val))
          (V (j+1) (child I i.val)) _ _ _ _ _ _ hp'
      · have hj1 : j+1<J := by omega
        simp only [physicalCarrier,virtualPhysicalCarrier,if_neg hd0,jointCarrier,selectedCarrier,virtualCarrier,padded,hyF,hyS]
        rw [hH j I hj]
        apply congrArg₂ (fun a b : ℝ => virtualH (G j I) (r j I) (columns j I) (block m j x.fst)-a+b)
        · exact Finset.sum_congr rfl (fun i _ => hr j I hj i)
        · apply Finset.sum_congr rfl
          intro i _
          exact congrArg₂ (fun a b : ℝ => a*b) (hr j I hj i) (hl (j+1) (child I i.val) hj1)
    | succ t =>
      change (∑ i : Fin ((G j I).n+1),(geometryWithFrames G V j I).selector i (block m j y.fst)*
        physicalCarrier m Q (geometryWithFrames G V) _ _ d (j+1) (child I i.val) t y)=_
      change _=∑ i : Fin ((G j I).n+1),virtualSelector (G j I) (r j I) (columns j I) i (block m j x.fst)*
        virtualPhysicalCarrier G r sourceCount columns sourceColumns targetColumns d (j+1) (child I i.val) t x
      apply Finset.sum_congr rfl
      intro i _
      rw [hs j I hj i,ih (j+1) (child I i.val) t (by omega)]

end Bilevel.EndpointTransportResponse
