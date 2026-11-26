import Bilevel.ChiHierarchyActiveInverse

/-! Quantitative strict blind margin at the actual nonlinear active inverse.
The bound follows from compact-normal comparison and old-space projection
geometry, leaving a uniform open neighborhood for virtual oracle equality. -/
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

include hm hWV htree hhp hw hfuture hcs hell hwidth hfinest hR in
theorem hierarchy_active_inverse_strict_blind
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
    let z := PartialLegendre.jointSolution (reassociated_gradient_lipschitz hFa (1/12) ha)
      (by change ((1/12:NNReal):ℝ)<1;norm_num : (1/12:NNReal)<1) a (u:Full (Blocks m F) s)
    ∀ j P,j≤J → ∀ k : Fin ((D j P).n+1),r j P≤k.val →
      |(D j P).coordinates (block m j z.fst) k|≤3*(D j P).width/16 := by
  dsimp only
  let hFa := hierarchyExtension_contDiff m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn
    (fun i => (htree (i.val+1) [] (by omega) (by have := i.isLt;omega)).width_pos)
  let hFi := hierarchyInactiveExtension_contDiff m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn
    (fun i => (htree (i.val+1) [] (by omega) (by have := i.isLt;omega)).width_pos)
  let p := restrictedInverse (normalKnown V s) (by change ((1/12:NNReal):ℝ)<1;norm_num : (1/12:NNReal)<1)
    (lowerSlice_gradient_lipschitz hFa (1/12) ha a)
    (subspaceInclusion (normalKnown W s) (normalKnown V s) (normalKnown_mono hWV) u) ⟨1,by norm_num⟩
  let p0 := restrictedInverse (normalKnown W s) (by change ((1/12:NNReal):ℝ)<1;norm_num : (1/12:NNReal)<1)
    (lowerSlice_gradient_lipschitz hFi (1/12) hi a) u ⟨1,by norm_num⟩
  have he := hierarchy_active_restricted_inverse_eq M D J hm W V hWV r htree hhp hw hfuture c v hc hcs hβ hv
    hell hwidth hfinest s index radialIndex fineIndex rad R dn hR hmargin hWlast ha hi a hfront u
  change (p:Full (Blocks m F) s)=_ at he
  rw [← he]
  have hd := hierarchy_homotopy_distance M D J hm W V hWV r htree hhp hw hfuture c v hc hcs hβ hv
    hell hwidth hfinest s index radialIndex fineIndex rad R dn hR ha hi a u ⟨1,by norm_num⟩
  change ‖(p:Full (Blocks m F) s)-(p0:Full (Blocks m F) s)‖≤_ at hd
  intro j P hj k hk
  let ij : Fin m := ⟨j,by omega⟩
  have hRj := (htree j P (by omega) (by omega)).radius_pos
  have hb := coordinate_near_normalKnown W (p:Full (Blocks m F) s) p0 ij (D j P) hRj k
    ((D j P).width/8) (6*width c (D J []).width v (levels v)/11) (hmargin j P hj k hk) hd
  have hwj := hWlast j P hj
  have hpj := (htree j P (by omega) (by omega)).width_pos
  have hblock : block m j (p:Full (Blocks m F) s).fst=(p:Full (Blocks m F) s).fst ij := by
    have hjm : j<m := by omega
    simp only [block,dif_pos hjm,PiLp.proj_apply]
    rfl
  rw [hblock]
  nlinarith

end Bilevel.ChiOuter
