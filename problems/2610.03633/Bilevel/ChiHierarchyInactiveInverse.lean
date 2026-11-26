import Bilevel.ChiCarrierProjectionBlind
import Bilevel.ChiExtensionRestrictedInverse

/-! Actual fixed inactive inverse locality from column-projection geometry.
The numeric blind conditions hold at every restricted point, hence in
particular at the constructed unique restricted inverse. There is no
assumption of small total hidden force relative to the finest width. -/
noncomputable section
set_option maxHeartbeats 600000
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiExtension ZeroChainSchedule
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
      width c (D J []).width θ (levels θ)/8)
  (s : ℕ) (coarseIndex radialIndex : Fin J → Fin s) (fineIndex : Fin s)
  (ρ R : ℕ → ℝ) (dn : ℝ) (hR : ∀ i : Fin J,0<R (i.val+1))

include hm htree hhp hw hfuture hcs hell hwidth hfinest hR in
theorem hierarchyInactive_gradient_invariant (a : E) (z : normalKnown W s) :
    gradient (lowerSlice (hierarchyInactiveExtension m M D J c θ hc hβ hθ s coarseIndex radialIndex fineIndex ρ R dn) a)
      (z:Full (Blocks m F) s)∈normalKnown W s := by
  let x := (z:Full (Blocks m F) s).fst
  have hx : x∈knownSpace W := z.property
  have ht : TreeBlind D 0 J (by simpa using hm) W x r := htree.at_point x hx
  have hz : ∀ P,∀ k : Fin ((D J P).n+1),r J P ≤ k.val →
      |(D J P).coordinates (x ⟨J,hm⟩) k|≤width c (D J []).width θ (levels θ)/8 :=
    inactive_tail_of_projection D ⟨J,hm⟩ W (r J) _
      (fun P => (htree J P (by omega) (by simp)).radius_pos) hfinest x (hx _)
  exact hierarchyInactiveExtension_normal_support M D J hm a x W hx r ht hhp hw hfuture
    c θ hc hcs hβ hθ hell hwidth hz s coarseIndex radialIndex fineIndex ρ R dn hR
      (z:Full (Blocks m F) s).snd

include hm htree hhp hw hfuture hcs hell hwidth hfinest hR in
theorem hierarchyInactive_restricted_inverse_eq [CompleteSpace (normalKnown W s)]
    (δ : NNReal)
    (hb : ∀ z,‖iteratedFDeriv ℝ 2
      (hierarchyInactiveExtension m M D J c θ hc hβ hθ s coarseIndex radialIndex fineIndex ρ R dn) z‖≤(δ:ℝ))
    (hδ : δ<1) (a : E) (u : normalKnown W s) :
    let hf := hierarchyInactiveExtension_contDiff m M D J c θ hc hβ hθ s coarseIndex radialIndex fineIndex ρ R dn
      (fun i => (htree (i.val+1) [] (by omega) (by have := i.isLt;omega)).width_pos)
    (NearIdentityInverse.restrictedInverse (normalKnown W s) hδ (lowerSlice_gradient_lipschitz hf δ hb a) u
      ⟨1,by norm_num⟩ : Full (Blocks m F) s)=
      PartialLegendre.jointSolution (reassociated_gradient_lipschitz hf δ hb) hδ a (u:Full (Blocks m F) s) := by
  dsimp only
  let hf := hierarchyInactiveExtension_contDiff m M D J c θ hc hβ hθ s coarseIndex radialIndex fineIndex ρ R dn
    (fun i => (htree (i.val+1) [] (by omega) (by have := i.isLt;omega)).width_pos)
  apply restricted_lowerSlice_eq_jointSolution (normalKnown W s) hf δ hb hδ a u
  exact hierarchyInactive_gradient_invariant M D J hm W r htree hhp hw hfuture
    c θ hc hcs hβ hθ hell hwidth hfinest s coarseIndex radialIndex fineIndex ρ R dn hR a _

end Bilevel.ChiOuter
