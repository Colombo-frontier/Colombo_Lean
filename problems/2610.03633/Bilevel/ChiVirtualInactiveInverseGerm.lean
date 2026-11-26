import Bilevel.ChiHierarchyInactiveMargin
import Bilevel.ChiVirtualInactiveGerm

/-! Actual fixed inactive inverse locality from column-projection geometry.
The numeric blind conditions hold at every restricted point, hence in
particular at the constructed unique restricted inverse. There is no
assumption of small total hidden force relative to the finest width. -/
noncomputable section
open scoped Topology
set_option maxHeartbeats 600000
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiExtension ZeroChainSchedule ChiOuter
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

variable {m : ℕ} (M : Node E) (D : Geometry F) (J : ℕ) (hm : J < m)
  (W : Fin m → Submodule ℝ F) [∀ i,CompleteSpace (W i)] (r : ℕ → List ℕ → ℕ)
  (htree : TreeProjection D 0 J (by simpa using hm) W r)
  (hhp : ∀ t,t < J → ∀ P,0<(D (t+1) P).parentWidth)
  (hw : ∀ t,t < J → ∀ P,(D (t+1) P).width≤(D (t+1) P).parentWidth)
  (hfuture : ∀ t,t < J → ∀ P,∀ i : Fin ((D t P).n+1),r t P ≤ i.val →
    r (t+1) (child P i.val)≤(D (t+1) (child P i.val)).n)
  (c θ : ℝ) (hc : 0<c) (hcs : c≤1/128) (hβ : 0<(D J []).width) (hθ : 1≤θ)
  (hell : ∀ P,0≤(D J P).ell) (hwidth : ∀ P,(D J P).width=(D J []).width)
  (hfinest : ∀ P,∀ k : Fin ((D J P).n+1),r J P ≤ k.val →
    (D J P).radius*‖(W ⟨J,hm⟩).orthogonalProjection ((D J P).frame (basis k))‖≤
      width c (D J []).width θ (levels θ)/16)
  (s : ℕ) (coarseIndex radialIndex : Fin J → Fin s) (fineIndex : Fin s)
  (ρ R : ℕ → ℝ) (dn : ℝ) (hR : ∀ i : Fin J,0<R (i.val+1))


include hm htree hhp hw hfuture hcs hell hwidth hfinest hR in
theorem hierarchy_inactive_germ_at_inverse [CompleteSpace (normalKnown W s)]
    (hmargin : ∀ j P (hj : j≤J),∀ k : Fin ((D j P).n+1),r j P≤k.val →
      (D j P).radius*‖(W ⟨j,by omega⟩).orthogonalProjection ((D j P).frame (basis k))‖≤(D j P).width/8)
    (hWlast : ∀ j P,j≤J → width c (D J []).width θ (levels θ)≤(D j P).width)
    (δ : NNReal)
    (hb : ∀ z,‖iteratedFDeriv ℝ 2
      (hierarchyInactiveExtension m M D J c θ hc hβ hθ s coarseIndex radialIndex fineIndex ρ R dn) z‖≤(δ:ℝ))
    (hδ : δ<1) (x : E) (u : normalKnown W s)
    (rM : ℕ) (macroColumns : Fin (M.n+1) → E) (columns : ∀ j I,Fin ((D j I).n+1) → F)
    (hmPrefix : ∀ k : Fin (M.n+1),k.val<rM → macroColumns k=M.frame (basis k))
    (hprefix : ∀ j I,∀ k : Fin ((D j I).n+1),k.val<r j I → columns j I k=(D j I).frame (basis k))
    (hmw : 0<M.width) (hmR : 0<M.radius)
    (hmacro : ∀ k : Fin (M.n+1),rM≤k.val → |M.coordinates x k|≤M.width/8)
    (hWM : width c (D J []).width θ (levels θ)≤M.width) :
    let hf := hierarchyInactiveExtension_contDiff m M D J c θ hc hβ hθ s coarseIndex radialIndex fineIndex ρ R dn
      (fun i => (htree (i.val+1) [] (by omega) (by have := i.isLt;omega)).width_pos)
    let z := PartialLegendre.jointSolution (reassociated_gradient_lipschitz hf δ hb) hδ x (u:Full (Blocks m F) s)
    hierarchyInactiveExtension m M D J c θ hc hβ hθ s coarseIndex radialIndex fineIndex ρ R dn =ᶠ[𝓝 (pack (pack x z.fst) z.snd)]
      virtualInactive m M D J rM r macroColumns columns c θ s coarseIndex radialIndex fineIndex ρ R dn := by
  dsimp only
  have hblind := hierarchy_inactive_inverse_strict_blind M D J hm W r htree hhp hw hfuture c θ hc hcs hβ hθ
    hell hwidth hfinest s coarseIndex radialIndex fineIndex ρ R dn hR hmargin δ hb hδ x u
  have hp := width_pos c (D J []).width θ hc hβ hθ (levels θ)
  apply actual_inactive_eventuallyEq_virtual (δ:=width c (D J []).width θ (levels θ)/16) m M D J rM r macroColumns columns hmPrefix hprefix hmw
    (fun j I hj => (htree j I (by omega) (by omega)).width_pos)
    c θ hc hcs hβ hθ hell hwidth s coarseIndex radialIndex fineIndex ρ R dn _
  · intro k hk
    have hh := hmacro k hk
    change |M.coordinates x k|≤3*M.width/16
    linarith
  · intro j I hj k hk
    have hh := hblind.1 j I hj k hk
    have hhpos := (htree j I (by omega) (by omega)).width_pos
    exact hh.trans (by linarith)
  · exact hblind.2
  · exact hhp
  · exact hw
  · exact hfuture
  · exact hmR
  · exact fun j I hj => (htree j I (by omega) (by omega)).radius_pos
  · positivity
  · linarith
  · intro j I hj
    have hh := hWlast j I hj
    linarith
  · exact le_rfl

end Bilevel.ChiPrefixEvaluation
