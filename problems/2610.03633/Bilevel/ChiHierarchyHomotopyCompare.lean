import Bilevel.ChiHierarchySignalSmall
import Bilevel.NearIdentityNestedComparison
import Bilevel.ChiProjectionStability

/-! Actual active/inactive hierarchy homotopies on nested disclosed spaces.
The inactive point stays in the old space by the constructed support proof.
Compact fine-normal support bounds their distance without hidden-force
smallness and without a total-radial-coefficient assumption. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Bilevel.ChiCarrier
open ChiExtension
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem normalKnown_mono {m s : ℕ} {W V : Fin m → Submodule ℝ F} (hWV : ∀ i,W i≤V i) :
    normalKnown W s≤normalKnown V s := by
  intro z hz i
  exact hWV i (hz i)

end Bilevel.ChiCarrier

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
theorem hierarchy_homotopy_distance
    (ha : ∀ z,‖iteratedFDeriv ℝ 2
      (hierarchyExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn) z‖≤1/12)
    (hi : ∀ z,‖iteratedFDeriv ℝ 2
      (hierarchyInactiveExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn) z‖≤1/12)
    (a : E) (u : normalKnown W s) (t : Time) :
    let hFa := hierarchyExtension_contDiff m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn
      (fun i => (htree (i.val+1) [] (by omega) (by have := i.isLt;omega)).width_pos)
    let hFi := hierarchyInactiveExtension_contDiff m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn
      (fun i => (htree (i.val+1) [] (by omega) (by have := i.isLt;omega)).width_pos)
    ‖(restrictedInverse (normalKnown V s) (by change ((1/12:NNReal):ℝ)<1; norm_num : (1/12:NNReal)<1)
      (lowerSlice_gradient_lipschitz hFa (1/12) ha a)
      (subspaceInclusion (normalKnown W s) (normalKnown V s) (normalKnown_mono hWV) u) t : Full (Blocks m F) s)-
      (restrictedInverse (normalKnown W s) (by change ((1/12:NNReal):ℝ)<1; norm_num : (1/12:NNReal)<1)
        (lowerSlice_gradient_lipschitz hFi (1/12) hi a) u t : Full (Blocks m F) s)‖≤
      6*width c (D J []).width v (levels v)/11 := by
  dsimp only
  let hFa := hierarchyExtension_contDiff m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn
    (fun i => (htree (i.val+1) [] (by omega) (by have := i.isLt;omega)).width_pos)
  let hFi := hierarchyInactiveExtension_contDiff m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn
    (fun i => (htree (i.val+1) [] (by omega) (by have := i.isLt;omega)).width_pos)
  let Wlast := width c (D J []).width v (levels v)
  have hh := nested_inverse_compare (normalKnown W s) (normalKnown V s) (normalKnown_mono hWV)
    (by change ((1/12:NNReal):ℝ)<1; norm_num : (1/12:NNReal)<1) (by change ((1/12:NNReal):ℝ)<1; norm_num : (1/12:NNReal)<1)
    (lowerSlice_gradient_lipschitz hFa (1/12) ha a) (lowerSlice_gradient_lipschitz hFi (1/12) hi a) u t
    (hierarchyInactive_gradient_invariant M D J hm W r htree hhp hw hfuture c v hc hcs hβ hv hell hwidth hfinest
      s index radialIndex fineIndex rad R dn hR a _) (Wlast/2) (fun z => ?_)
  · exact hh.trans_eq (by norm_num;ring)
  · have hs := hierarchy_lower_signal_bound m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn
      (fun i => (htree (i.val+1) [] (by omega) (by have := i.isLt;omega)).width_pos)
      (1/12) (1/12) ha hi a z
    exact hs.trans_eq (by norm_num;dsimp [Wlast];ring)

end Bilevel.ChiOuter
