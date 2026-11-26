import Bilevel.ChiHierarchyHomotopyConfinement
import Bilevel.ChiHierarchyFrontierNormal

/-! Actual active restricted inverse locality for the same full hierarchy.
A finite prefix certificate identifies the unfinished frontier. Coordinate
confinement is proved by compact-normal active/inactive comparison, so the
proof requires no hidden-force/blind-width ratio. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiExtension ZeroChainSchedule NearIdentityInverse
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

variable {m : ℕ} (M : Node E) (D : Geometry F) (J : ℕ) (hm : J<m)
  (W V : Fin m → Submodule ℝ F) [∀ i,CompleteSpace (W i)]
  (hWV : ∀ i,W i≤V i) (r : ℕ → List ℕ → ℕ)
  (htree : TreeProjection D 0 J (by simpa using hm) W r)
  (hhp : ∀ t,t<J → ∀ P,0<(D (t+1) P).parentWidth)
  (hw : ∀ t,t<J → ∀ P,(D (t+1) P).width≤(D (t+1) P).parentWidth)
  (hfuture : ∀ t,t<J → ∀ P,∀ i : Fin ((D t P).n+1),r t P ≤ i.val →
    r (t+1) (child P i.val)≤(D (t+1) (child P i.val)).n)
  (c v : ℝ) (hc : 0<c) (hcs : c≤1/128) (hβ : 0<(D J []).width) (hv : 1≤v)
  (hell : ∀ P,0≤(D J P).ell) (hwidth : ∀ P,(D J P).width=(D J []).width)
  (hfinest : ∀ P,∀ k : Fin ((D J P).n+1),r J P ≤ k.val →
    (D J P).radius*‖(W ⟨J,hm⟩).orthogonalProjection ((D J P).frame (basis k))‖≤
      width c (D J []).width v (levels v)/8)
  (s : ℕ) (index radialIndex : Fin J → Fin s) (fineIndex : Fin s)
  (rad R : ℕ → ℝ) (dn : ℝ) (hR : ∀ i : Fin J,0<R (i.val+1))
  [CompleteSpace (normalKnown W s)] [CompleteSpace (normalKnown V s)]

include hm htree hhp hw hfuture hcs hell hwidth hfinest hR in
theorem hierarchy_active_homotopy_gradient_mem
    (hmargin : ∀ j P (hj : j≤J),∀ k : Fin ((D j P).n+1),r j P≤k.val →
      (D j P).radius*‖(W ⟨j,by omega⟩).orthogonalProjection ((D j P).frame (basis k))‖≤(D j P).width/8)
    (hWlast : ∀ j P,j≤J → width c (D J []).width v (levels v)≤(D j P).width/128)
    (ha : ∀ z,‖iteratedFDeriv ℝ 2
      (hierarchyExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn) z‖≤1/12)
    (hi : ∀ z,‖iteratedFDeriv ℝ 2
      (hierarchyInactiveExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn) z‖≤1/12)
    (a : E) (hfront : FrontierKnown D r (V ⟨J,hm⟩) J 0 [(outerValueStage M a).val])
    (u : normalKnown W s) (t : Time) :
    let hFa := hierarchyExtension_contDiff m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn
      (fun i => (htree (i.val+1) [] (by omega) (by have := i.isLt;omega)).width_pos)
    let p := restrictedInverse (normalKnown V s) (by change ((1/12:NNReal):ℝ)<1; norm_num : (1/12:NNReal)<1)
      (lowerSlice_gradient_lipschitz hFa (1/12) ha a)
      (subspaceInclusion (normalKnown W s) (normalKnown V s) (normalKnown_mono hWV) u) t
    gradient (lowerSlice (hierarchyExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn) a)
      (p:Full (Blocks m F) s)∈normalKnown V s := by
  dsimp only
  let hFa := hierarchyExtension_contDiff m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn
      (fun i => (htree (i.val+1) [] (by omega) (by have := i.isLt;omega)).width_pos)
  let p := restrictedInverse (normalKnown V s) (by change ((1/12:NNReal):ℝ)<1; norm_num : (1/12:NNReal)<1)
      (lowerSlice_gradient_lipschitz hFa (1/12) ha a)
      (subspaceInclusion (normalKnown W s) (normalKnown V s) (normalKnown_mono hWV) u) t
  have ht := hierarchy_homotopy_blind M D J hm W V hWV r htree hhp hw hfuture c v hc hcs hβ hv hell hwidth hfinest
    s index radialIndex fineIndex rad R dn hR hmargin hWlast ha hi a u t
  exact hierarchyExtension_frontier_normal_support M D J hm a (p:Full (Blocks m F) s).fst V
    p.property r ht hhp hw hfuture c v hc hcs hβ hv hell hfront s index radialIndex fineIndex rad R dn hR
    (p:Full (Blocks m F) s).snd

include hm htree hhp hw hfuture hcs hell hwidth hfinest hR in
theorem hierarchy_active_restricted_inverse_eq
    (hmargin : ∀ j P (hj : j≤J),∀ k : Fin ((D j P).n+1),r j P≤k.val →
      (D j P).radius*‖(W ⟨j,by omega⟩).orthogonalProjection ((D j P).frame (basis k))‖≤(D j P).width/8)
    (hWlast : ∀ j P,j≤J → width c (D J []).width v (levels v)≤(D j P).width/128)
    (ha : ∀ z,‖iteratedFDeriv ℝ 2
      (hierarchyExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn) z‖≤1/12)
    (hi : ∀ z,‖iteratedFDeriv ℝ 2
      (hierarchyInactiveExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn) z‖≤1/12)
    (a : E) (hfront : FrontierKnown D r (V ⟨J,hm⟩) J 0 [(outerValueStage M a).val])
    (u : normalKnown W s) :
    let hFa := hierarchyExtension_contDiff m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn
      (fun i => (htree (i.val+1) [] (by omega) (by have := i.isLt;omega)).width_pos)
    (restrictedInverse (normalKnown V s) (by change ((1/12:NNReal):ℝ)<1; norm_num : (1/12:NNReal)<1)
      (lowerSlice_gradient_lipschitz hFa (1/12) ha a)
      (subspaceInclusion (normalKnown W s) (normalKnown V s) (normalKnown_mono hWV) u)
      ⟨1,by norm_num⟩ : Full (Blocks m F) s)=
      PartialLegendre.jointSolution (reassociated_gradient_lipschitz hFa (1/12) ha) (by change ((1/12:NNReal):ℝ)<1; norm_num : (1/12:NNReal)<1) a (u:Full (Blocks m F) s) := by
  dsimp only
  let hFa := hierarchyExtension_contDiff m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn
      (fun i => (htree (i.val+1) [] (by omega) (by have := i.isLt;omega)).width_pos)
  apply restricted_lowerSlice_eq_jointSolution (normalKnown V s) hFa (1/12) ha (by change ((1/12:NNReal):ℝ)<1; norm_num : (1/12:NNReal)<1) a
    (subspaceInclusion (normalKnown W s) (normalKnown V s) (normalKnown_mono hWV) u)
  exact hierarchy_active_homotopy_gradient_mem M D J hm W V hWV r htree hhp hw hfuture c v hc hcs hβ hv hell hwidth hfinest
    s index radialIndex fineIndex rad R dn hR hmargin hWlast ha hi a hfront u ⟨1,by norm_num⟩

end Bilevel.ChiOuter
