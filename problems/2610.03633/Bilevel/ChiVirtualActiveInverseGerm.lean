import Bilevel.ChiHierarchyInverseMargin
import Bilevel.ChiVirtualActiveGerm

/-! Quantitative strict blind margin at the actual nonlinear active inverse.
The bound follows from compact-normal comparison and old-space projection
geometry, leaving a uniform open neighborhood for virtual oracle equality. -/
noncomputable section
open scoped Topology
set_option maxHeartbeats 1200000
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiExtension ZeroChainSchedule NearIdentityInverse ChiOuter ChiTreeProgress
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
theorem hierarchy_active_germ_at_inverse
    (hmargin : ∀ j P (hj : j≤J),∀ k : Fin ((D j P).n+1),r j P≤k.val →
      (D j P).radius*‖(W ⟨j,by omega⟩).orthogonalProjection ((D j P).frame (basis k))‖≤(D j P).width/8)
    (hWlast : ∀ j P,j≤J → width c (D J []).width v (levels v)≤(D j P).width/128)
    (ha : ∀ z,‖iteratedFDeriv ℝ 2
      (hierarchyExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn) z‖≤1/12)
    (hi : ∀ z,‖iteratedFDeriv ℝ 2
      (hierarchyInactiveExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn) z‖≤1/12)
    (x : E) (hfront : FrontierKnown D r (V ⟨J,hm⟩) J 0 [(outerValueStage M x).val])
    (u : normalKnown W s)
    (rM sM : ℕ) (a : ℕ → List ℕ → ℕ)
    (macroColumns : Fin (M.n+1) → E) (columns : ∀ j I,Fin ((D j I).n+1) → F)
    (hmPrefix : ∀ k : Fin (M.n+1),k.val<sM → macroColumns k=M.frame (basis k))
    (hprefix : ∀ j I,∀ k : Fin ((D j I).n+1),k.val<a j I → columns j I k=(D j I).frame (basis k))
    (hms : rM≤sM) (hra : ∀ j I,r j I≤a j I)
    (hmw : 0<M.width) (hmR : 0<M.radius)
    (hmacro : ∀ k : Fin (M.n+1),rM≤k.val → |M.coordinates x k|≤M.width/8)
    (hWM : width c (D J []).width v (levels v)≤M.width)
    (hafuture : ∀ t,t<J → ∀ I,∀ i : Fin ((D t I).n+1),a t I ≤ i.val →
      a (t+1) (child I i.val)≤(D (t+1) (child I i.val)).n)
    (hadvance : ∀ i : Fin (M.n+1),i.val≤rM → FrontierAdvance D r a J 0 [i.val]) :
    let hf := hierarchyExtension_contDiff m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn
      (fun i => (htree (i.val+1) [] (by omega) (by have := i.isLt;omega)).width_pos)
    let z := PartialLegendre.jointSolution (reassociated_gradient_lipschitz hf (1/12) ha)
      (by change ((1/12:NNReal):ℝ)<1;norm_num : (1/12:NNReal)<1) x (u:Full (Blocks m F) s)
    hierarchyExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn =ᶠ[𝓝 (pack (pack x z.fst) z.snd)]
      virtualActive m M D J sM a macroColumns columns c v s index radialIndex fineIndex rad R dn := by
  dsimp only
  have hblind := hierarchy_active_inverse_strict_blind M D J hm W V hWV r htree hhp hw hfuture c v hc hcs hβ hv
    hell hwidth hfinest s index radialIndex fineIndex rad R dn hR hmargin hWlast ha hi x hfront u
  have hp := width_pos c (D J []).width v hc hβ hv (levels v)
  apply actual_active_eventuallyEq_virtual (δ:=width c (D J []).width v (levels v)/16) m M D J rM sM r a macroColumns columns hmPrefix hprefix hms hra hmw
    (fun j I hj => (htree j I (by omega) (by omega)).width_pos) hhp hw hafuture hadvance
    c v hc hcs hβ hv hell s index radialIndex fineIndex rad R dn _
  · intro k hk
    have hh := hmacro k hk
    change |M.coordinates x k|≤3*M.width/16
    linarith
  · exact hblind
  · exact hmR
  · exact fun j I hj => (htree j I (by omega) (by omega)).radius_pos
  · positivity
  · linarith
  · intro j I hj
    have hh := hWlast j I hj
    have hhpos := (htree j I (by omega) (by omega)).width_pos
    linarith

end Bilevel.ChiPrefixEvaluation
