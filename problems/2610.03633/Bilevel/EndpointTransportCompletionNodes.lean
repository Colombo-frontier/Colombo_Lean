import Bilevel.EndpointTransportCompletedReadout
import Bilevel.ChiSourceAuxiliaryFrame

/-! Cross-dimension source nodes and isometric product embeddings used to
transfer the full completed physical hierarchy to its prefix formula. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry ChiBoundedChain ChiPrefixEvaluation ChiCarrier ChiRecursive ChiExtension
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def nodeWithFrame (N : Node E) (V : Space N.n →ₗᵢ[ℝ] F) : Node F where
  n := N.n
  ell := N.ell
  width := N.width
  receiver := N.receiver
  nu := N.nu
  force := N.force
  parentWidth := N.parentWidth
  tailRadius := N.tailRadius
  radius := N.radius
  frame := V

def geometryWithFrames (G : Geometry E) (V : ∀ j I,Space (G j I).n →ₗᵢ[ℝ] F) : Geometry F :=
  fun j I => nodeWithFrame (G j I) (V j I)

omit [CompleteSpace E] [CompleteSpace F] in
theorem compress_isometry (I : E →ₗᵢ[ℝ] F) (R : ℝ) (x : E) :
    RadialWrapper.compress R (I x)=I (RadialWrapper.compress R x) := by
  simp only [RadialWrapper.compress,RadialWrapper.scale,I.norm_map,map_smul]

theorem coordinates_isometry (I : E →ₗᵢ[ℝ] F) {a : ℕ} (U : Space a →ₗᵢ[ℝ] E)
    (R : ℝ) (x : E) :
    WrappedChain.coordinates a R (I.comp U) (I x)=WrappedChain.coordinates a R U x := by
  ext k
  rw [coordinates_inner,coordinates_inner,compress_isometry]
  exact I.inner_map_map _ _

def completedOrdinaryNode {D K : ℕ} (N : Node (Block D)) (r : ℕ)
    (columns : Fin (N.n+1) → Block D) (aux : Space N.n →ₗᵢ[ℝ] Space K)
    (hGram : ∀ a b : Fin (N.n+1),a.val<r → b.val<r → ⟪columns a,columns b⟫=if a=b then 1 else 0) :
    Node (Block (completionDimension D K)) :=
  nodeWithFrame N ((completionBlockEquiv D K).toLinearIsometry.comp
    (completionFrame N.n r columns aux hGram))

theorem completedOrdinaryNode_coordinates {D K : ℕ} (N : Node (Block D)) (r : ℕ)
    (columns : Fin (N.n+1) → Block D) (aux : Space N.n →ₗᵢ[ℝ] Space K)
    (hGram : ∀ a b : Fin (N.n+1),a.val<r → b.val<r → ⟪columns a,columns b⟫=if a=b then 1 else 0)
    (x : Block D) :
    (completedOrdinaryNode N r columns aux hGram).coordinates (completionBlockInclusion D K x)=
      readout N.n r N.radius columns x := by
  change WrappedChain.coordinates N.n N.radius ((completionBlockEquiv D K).toLinearIsometry.comp
    (completionFrame N.n r columns aux hGram)) (completionBlockEquiv D K (pack x 0))=_
  exact (coordinates_isometry (completionBlockEquiv D K).toLinearIsometry
    (completionFrame N.n r columns aux hGram) N.radius (pack x 0)).trans
    (completion_coordinates N.n r N.radius columns aux hGram x)

def blocksMap (m : ℕ) (I : E →ₗᵢ[ℝ] F) : Blocks m E →ₗᵢ[ℝ] Blocks m F where
  toLinearMap :=
    { toFun := fun x => (WithLp.equiv 2 (Fin m → F)).symm (fun j => I (x j))
      map_add' := by intro x y;ext j;simp
      map_smul' := by intro c x;ext j;simp }
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← real_inner_self_eq_norm_sq,← real_inner_self_eq_norm_sq,PiLp.inner_apply,PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro j _
    exact I.inner_map_map (x j) (x j)

omit [CompleteSpace E] [CompleteSpace F] in
theorem blocksMap_apply (m : ℕ) (I : E →ₗᵢ[ℝ] F) (x : Blocks m E) (j : Fin m) :
    blocksMap m I x j=I (x j) := rfl

omit [CompleteSpace E] [CompleteSpace F] in
theorem block_blocksMap (m j : ℕ) (I : E →ₗᵢ[ℝ] F) (x : Blocks m E) :
    block m j (blocksMap m I x)=I (block m j x) := by
  by_cases hj : j<m
  · simp only [block,dif_pos hj,PiLp.proj_apply,blocksMap_apply]
  · simp only [block,dif_neg hj,ContinuousLinearMap.zero_apply,map_zero]

def completionTangentMap {J n D D' : ℕ} (I : Block D →ₗᵢ[ℝ] Block D') :
    HybridTangent (Blocks J (Block D)) n D →ₗᵢ[ℝ] HybridTangent (Blocks J (Block D')) n D' :=
  jointMap (blocksMap J I) (physicalMap I)

def completionBaseMap {J n D D' : ℕ} (M : E →ₗᵢ[ℝ] F) (I : Block D →ₗᵢ[ℝ] Block D') :
    PhysicalBase E J n D →ₗᵢ[ℝ] PhysicalBase F J n D' :=
  jointMap M (completionTangentMap I)

def completionFullMap {J n D D' : ℕ} (s : ℕ) (M : E →ₗᵢ[ℝ] F) (I : Block D →ₗᵢ[ℝ] Block D') :
    Full (PhysicalBase E J n D) s →ₗᵢ[ℝ] Full (PhysicalBase F J n D') s :=
  jointMap (completionBaseMap M I) (LinearIsometryEquiv.refl ℝ (Normals s)).toLinearIsometry

end Bilevel.EndpointTransportResponse
