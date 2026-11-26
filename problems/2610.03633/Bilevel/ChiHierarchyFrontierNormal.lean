import Bilevel.ChiHierarchyFrontierTangent
import Bilevel.ChiExtensionSliceInverse

/-! Actual full lower-space gradient support. All normal coordinates remain
public; the tangential coordinates lie in the finite disclosed product.
The gradient is that of the real macro-fixed hierarchy extension. -/
noncomputable section
set_option maxHeartbeats 600000
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiExtension
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem hierarchyExtension_frontier_normal_support {m : ℕ} (M : Node E) (D : Geometry F) (J : ℕ)
    (hm : J < m) (a : E) (x : Blocks m F) (W : Fin m → Submodule ℝ F)
    (hx : x∈knownSpace W) (r : ℕ → List ℕ → ℕ)
    (htree : TreeBlind D 0 J (by simpa using hm) W x r)
    (hhp : ∀ t,t < J → ∀ P,0<(D (t+1) P).parentWidth)
    (hw : ∀ t,t < J → ∀ P,(D (t+1) P).width≤(D (t+1) P).parentWidth)
    (hfuture : ∀ t,t < J → ∀ P,∀ i : Fin ((D t P).n+1),r t P ≤ i.val →
      r (t+1) (child P i.val)≤(D (t+1) (child P i.val)).n)
    (c θ : ℝ) (hc : 0<c) (hcs : c≤1/128) (hβ : 0<(D J []).width) (hθ : 1≤θ)
    (hell : ∀ P,0≤(D J P).ell)
    (hfront : FrontierKnown D r (W ⟨J,hm⟩) J 0 [(outerValueStage M a).val])
    (s : ℕ) (coarseIndex radialIndex : Fin J → Fin s) (fineIndex : Fin s)
    (ρ R : ℕ → ℝ) (dn : ℝ) (hR : ∀ i : Fin J,0<R (i.val+1)) (q : Normals s) :
    gradient (lowerSlice (hierarchyExtension m M D J c θ hc hβ hθ s coarseIndex radialIndex fineIndex ρ R dn) a)
      (pack x q)∈normalKnown W s := by
  have hf := hierarchyExtension_contDiff m M D J c θ hc hβ hθ s coarseIndex radialIndex fineIndex ρ R dn
    (fun i => (htree (i.val+1) [] (by omega) (by have := i.isLt;omega)).width_pos)
  apply (gradient_normalKnown_iff W x q ((lowerSlice_contDiff hf a).differentiable (by norm_num) _)).mpr
  exact hierarchyExtension_frontier_tangent_support M D J hm a x W hx r htree hhp hw hfuture
    c θ hc hcs hβ hθ hell hfront s coarseIndex radialIndex fineIndex ρ R dn hR q

end Bilevel.ChiOuter
