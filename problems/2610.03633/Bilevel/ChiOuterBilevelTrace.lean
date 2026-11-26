import Bilevel.ChiOuterExtensionTrace
import Bilevel.ChiExtensionResponse

/-! The actual partial-Legendre lower objective and upper readout recover
the recursive objective at its unique lower response. The sole remaining
analytic input is the extension Hessian bound, supplied by the source
extension-budget theorem. -/
noncomputable section
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiExtension
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def hierarchyUpper (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (J : ℕ) (ρ R : ℕ → ℝ)
    (s : ℕ) (dn : ℝ) (x : E) (y : Joint (Blocks m F) (Normals s)) : ℝ :=
  upperBase m M ν D J (ρ 0) (R 0) (pack x y.fst)+dn*normalReadout s y.snd

theorem hierarchyUpper_response_value (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (j : ℕ)
    (c θ : ℝ) (hc : 0<c) (hβ : 0<(D (j+1) []).width) (hθ : 1≤θ)
    (s : ℕ) (coarseIndex radialIndex : Fin (j+1) → Fin s) (fineIndex : Fin s)
    (ρ R : ℕ → ℝ) (dn : ℝ) (hdn : dn≠0)
    (hw : ∀ i : Fin (j+1),0<(D (i.val+1) []).width)
    (hR : ∀ i : Fin (j+1),0<R (i.val+1)) (K : ℝ) (x : E) (v : Blocks m F) :
    let Ext := hierarchyExtension m M D (j+1) c θ hc hβ hθ s coarseIndex radialIndex fineIndex ρ R dn
    hierarchyUpper m M ν D (j+1) ρ R s dn x (pack (K • v) (normalTrace Ext x (K • v)))=
      jointOuter m M ν D ρ R (j+1) K (pack x v) := by
  dsimp only
  have ht := hierarchyExtension_objective_trace m M ν D j c θ hc hβ hθ s coarseIndex radialIndex fineIndex
    ρ R dn hdn hw hR (pack x (K • v))
  change hierarchyUpper m M ν D (j+1) ρ R s dn x
    (pack (K • v) (normalTrace _ x (K • v)))=_
  change upperBase m M ν D (j+1) (ρ 0) (R 0) (pack x (K • v))+
    dn*normalReadout s (gradient (fun q : Normals s =>
      hierarchyExtension m M D (j+1) c θ hc hβ hθ s coarseIndex radialIndex fineIndex ρ R dn
        (pack (pack x (K • v)) q)) 0)=_
  rw [ht]
  simp only [jointOuter,one_smul]
  rfl

theorem hierarchy_lower_unique_mean_trace (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (j : ℕ)
    (c θ : ℝ) (hc : 0<c) (hβ : 0<(D (j+1) []).width) (hθ : 1≤θ)
    (s : ℕ) (coarseIndex radialIndex : Fin (j+1) → Fin s) (fineIndex : Fin s)
    (ρ R : ℕ → ℝ) (dn : ℝ) (hdn : dn≠0)
    (hw : ∀ i : Fin (j+1),0<(D (i.val+1) []).width)
    (hR : ∀ i : Fin (j+1),0<R (i.val+1))
    (δ : NNReal) (hδ : δ<1) (m0 cxy : ℝ) (hm0 : 0<m0) (x : E) (v : Blocks m F) :
    let Ext := hierarchyExtension m M D (j+1) c θ hc hβ hθ s coarseIndex radialIndex fineIndex ρ R dn
    let hExt := hierarchyExtension_contDiff m M D (j+1) c θ hc hβ hθ s coarseIndex radialIndex fineIndex ρ R dn hw
    ∀ hb : ∀ z,‖iteratedFDeriv ℝ 2 Ext z‖≤(δ:ℝ),
    let lower := extensionLower Ext hExt δ hb hδ m0 cxy x v
    ∃ y,(∀ w,lower y≤lower w) ∧ (∀ w,(∀ q,lower w≤lower q) → w=y) ∧
      hierarchyUpper m M ν D (j+1) ρ R s dn x y=jointOuter m M ν D ρ R (j+1) (cxy/m0) (pack x v) := by
  dsimp only
  intro hb
  let Ext := hierarchyExtension m M D (j+1) c θ hc hβ hθ s coarseIndex radialIndex fineIndex ρ R dn
  have hExt := hierarchyExtension_contDiff m M D (j+1) c θ hc hβ hθ s coarseIndex radialIndex fineIndex ρ R dn hw
  have hzero : ∀ p,Ext (pack p 0)=0 :=
    hierarchyExtension_zero_trace m M D (j+1) c θ hc hβ hθ s coarseIndex radialIndex fineIndex ρ R dn hw
  refine ⟨pack ((cxy/m0) • v) (normalTrace Ext x ((cxy/m0) • v)),?_,?_,?_⟩
  · intro w
    exact extensionLower_response_minimizes Ext hExt δ hb hδ hzero hm0 cxy x v w
  · intro w hw
    exact (extensionLower_unique_response Ext hExt δ hb hδ hzero hm0 cxy x v w).mp hw
  · exact hierarchyUpper_response_value m M ν D j c θ hc hβ hθ s coarseIndex radialIndex fineIndex
      ρ R dn hdn hw hR (cxy/m0) x v

end Bilevel.ChiOuter
