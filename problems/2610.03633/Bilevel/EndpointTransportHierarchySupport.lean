import Bilevel.EndpointTransportCoarseSupport
import Bilevel.EndpointTransportSelectedSupport
import Bilevel.EndpointTransportSliceIdentity
import Bilevel.ChiCarrierProjectionBlind
import Bilevel.ChiReleasedFrontierSupport

/-! Source-specific support of the actual macro-selected physical hierarchy.
The static premises concern only prefixes, column projections, positive
scales, and unfinished descendants. They do not assume any gradient support.
Only reachable fine branches consume a new source endpoint column. -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  PrimitiveGeometry PartialLegendre

structure PhysicalPrefixGeometry {J n D : ℕ} (Q : Rotations n D)
    (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (W : Fin J → Submodule ℝ (Block D)) (Z : Index n → Submodule ℝ (Block D))
    (r : ℕ → List ℕ → ℕ) : Prop where
  ancestors : ∀ k A,∀ hk : k<J,ProjectedBlindNode W ⟨k,hk⟩ (G k A) (r k A)
  width_pos : ∀ A,0<(G J A).width
  radius_pos : ∀ A,0<(G J A).radius
  parent_pos : ∀ k A,k≤J → 0<(G k A).parentWidth
  width_le_parent : ∀ k A,k≤J → (G k A).width≤(G k A).parentWidth
  fine_ell : ∀ A,P.ℓ=(G J A).ell
  fine_width : ∀ A,P.β=(G J A).width
  source_old : ∀ A,∀ k : Fin ((G J A).n+1),k.val<r J A → Q 0 ((G J A).frame (basis k))∈Z 0
  target_old : ∀ A,∀ k : Fin ((G J A).n+1),k.val<r J A →
    Q (Fin.last (n+1)) ((G J A).frame (basis k))∈Z (Fin.last (n+1))
  target_blind : ∀ A,∀ k : Fin ((G J A).n+1),r J A≤k.val →
    (gamma n*(G J A).radius)*‖(Z (Fin.last (n+1))).orthogonalProjection
      (Q (Fin.last (n+1)) ((G J A).frame (basis k)))‖≤(G J A).width/8
  future : ∀ k,k<J → ∀ A,∀ i : Fin ((G k A).n+1),r k A≤ i.val →
    r (k+1) (child A i.val)≤(G (k+1) (child A i.val)).n

theorem PhysicalPrefixGeometry.coarse_support {J n D : ℕ} {Q : Rotations n D}
    {G : Geometry (Block D)} {P : ChiFine.Parameters}
    {W : Fin J → Submodule ℝ (Block D)} {Z : Index n → Submodule ℝ (Block D)}
    {r : ℕ → List ℕ → ℕ} (h : PhysicalPrefixGeometry Q G P W Z r)
    (t : ℕ) (ht : t≤J) (I : List ℕ)
    (x : HybridTangent (Blocks J (Block D)) n D) (hx : x∈physicalTangentKnown W Z) :
    gradient (physicalCoarseCarrier J Q G jointFstLinear jointSndLinear P J 0 I t) x∈physicalTangentKnown W Z := by
  have hx' := (mem_physicalTangentKnown W Z x).mp hx
  exact physicalCoarseCarrier_support Q G P J t I le_rfl ht W Z x r
    (fun k A hk => (h.ancestors k A hk).at_point x.fst (hx'.1 _))
    h.width_pos h.radius_pos h.parent_pos h.width_le_parent h.fine_ell h.fine_width
    h.source_old h.target_old h.target_blind hx'.2 h.future

theorem PhysicalPrefixGeometry.fine_support {J n D : ℕ} {Q : Rotations n D}
    {G : Geometry (Block D)} {P : ChiFine.Parameters}
    {W : Fin J → Submodule ℝ (Block D)} {Z : Index n → Submodule ℝ (Block D)}
    {r : ℕ → List ℕ → ℕ} (h : PhysicalPrefixGeometry Q G P W Z r)
    (p : ℕ) (I : List ℕ)
    (hfront : FrontierKnown G r (Submodule.comap (Q 0).toLinearMap (Z 0)) J 0 I)
    (x : HybridTangent (Blocks J (Block D)) n D) (hx : x∈physicalTangentKnown W Z) :
    gradient (selectedPhysicalFinePiece J G jointFstLinear jointSndLinear Q P p J 0 I) x∈physicalTangentKnown W Z := by
  have hx' := (mem_physicalTangentKnown W Z x).mp hx
  apply selectedPhysicalFinePiece_frontier_support Q G P p J 0 I (by omega) W Z x r
    (fun k A _ hk => (h.ancestors k A (by omega)).at_point x.fst (hx'.1 _)) hfront
    (by rw [Nat.zero_add]; exact h.radius_pos)
    (by rw [Nat.zero_add]; exact h.source_old)
    (by rw [Nat.zero_add]; exact h.target_old) _ hx'.2
  rw [Nat.zero_add]
  intro A k hk
  rw [h.fine_width A]
  exact h.target_blind A k hk

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem physicalHierarchyCoarse_tangent_support {J n D : ℕ} (Q : Rotations n D) (M : Node E)
    (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (W : Fin J → Submodule ℝ (Block D)) (Z : Index n → Submodule ℝ (Block D))
    (r : ℕ → List ℕ → ℕ) (h : PhysicalPrefixGeometry Q G P W Z r)
    (i : Fin J) (a : E) (x : HybridTangent (Blocks J (Block D)) n D)
    (hx : x∈physicalTangentKnown W Z) :
    gradient (fun y => physicalHierarchyCoarse Q M G P J i (pack a y)) x∈physicalTangentKnown W Z := by
  have heq : (fun y => physicalHierarchyCoarse Q M G P J i (pack a y))=
      (fun y : HybridTangent (Blocks J (Block D)) n D => ∑ l : Fin (M.n+1),wrappedSelector M l a*
        physicalCoarseCarrier J Q G jointFstLinear jointSndLinear P J 0 [l.val] (i.val+1) y) :=
    funext (physicalHierarchyCoarse_slice Q M G P i a)
  rw [heq]
  apply gradient_sum_mem Finset.univ (physicalTangentKnown W Z)
    (fun l y => wrappedSelector M l a * physicalCoarseCarrier J Q G jointFstLinear jointSndLinear P J 0 [l.val] (i.val+1) y)
    (fun l => contDiff_const.mul
      (physicalCoarseCarrier_contDiff (X:=HybridTangent (Blocks J (Block D)) n D) J Q G jointFstLinear jointSndLinear P J 0 [l.val] (i.val+1))) x
  intro l _
  exact gradient_mul_mem (physicalTangentKnown W Z) (f:=fun _ => wrappedSelector M l a)
    (g:=physicalCoarseCarrier J Q G jointFstLinear jointSndLinear P J 0 [l.val] (i.val+1)) contDiff_const
    (physicalCoarseCarrier_contDiff (X:=HybridTangent (Blocks J (Block D)) n D) J Q G jointFstLinear jointSndLinear P J 0 [l.val] (i.val+1)) x
    (gradient_const_mem _ _ x) (h.coarse_support (i.val+1) (by omega) [l.val] x hx)

theorem physicalHierarchyFine_tangent_support {J n D : ℕ} (Q : Rotations n D) (M : Node E)
    (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (W : Fin J → Submodule ℝ (Block D)) (Z : Index n → Submodule ℝ (Block D))
    (r : ℕ → List ℕ → ℕ) (h : PhysicalPrefixGeometry Q G P W Z r)
    (rM : ℕ) (a : E) (hmw : 0<M.width)
    (hmacro : ∀ k : Fin (M.n+1),rM≤k.val → |M.coordinates a k|≤M.width/8)
    (hfront : ∀ i : Fin (M.n+1),i.val≤rM →
      FrontierKnown G r (Submodule.comap (Q 0).toLinearMap (Z 0)) J 0 [i.val])
    (p : ℕ) (x : HybridTangent (Blocks J (Block D)) n D) (hx : x∈physicalTangentKnown W Z) :
    gradient (fun y => (physicalHierarchyFine Q M G P J).e p (pack a y)) x∈physicalTangentKnown W Z := by
  have heq : (fun y => (physicalHierarchyFine Q M G P J).e p (pack a y))=
      (fun y : HybridTangent (Blocks J (Block D)) n D => ∑ l : Fin (M.n+1),wrappedSelector M l a*
        selectedPhysicalFinePiece J G jointFstLinear jointSndLinear Q P p J 0 [l.val] y) :=
    funext (physicalHierarchyFine_piece_slice Q M G P p a)
  rw [heq]
  apply gradient_sum_mem Finset.univ (physicalTangentKnown W Z)
    (fun l y => wrappedSelector M l a * selectedPhysicalFinePiece J G jointFstLinear jointSndLinear Q P p J 0 [l.val] y)
    (fun l => contDiff_const.mul
      (selectedPhysicalFinePiece_contDiff (X:=HybridTangent (Blocks J (Block D)) n D) J G jointFstLinear jointSndLinear Q P p J 0 [l.val])) x
  intro l _
  by_cases hl : l.val≤rM
  · exact gradient_mul_mem (physicalTangentKnown W Z) (f:=fun _ => wrappedSelector M l a)
      (g:=selectedPhysicalFinePiece J G jointFstLinear jointSndLinear Q P p J 0 [l.val]) contDiff_const
      (selectedPhysicalFinePiece_contDiff (X:=HybridTangent (Blocks J (Block D)) n D) J G jointFstLinear jointSndLinear Q P p J 0 [l.val]) x
      (gradient_const_mem _ _ x) (h.fine_support p [l.val] (hfront l hl) x hx)
  · have hz : wrappedSelector M l a=0 := by
      apply ChiPrefixEvaluation.outer_selector_future_zero M.n rM _ _ _ (by omega)
      intro k hk
      apply ZeroChainResidualScaled.scaled_coordinate_small M.width hmw (M.coordinates a) k
      have hh := hmacro k hk
      linarith
    simp only [hz,zero_mul]
    exact gradient_const_mem _ _ x

end Bilevel.EndpointTransportResponse

