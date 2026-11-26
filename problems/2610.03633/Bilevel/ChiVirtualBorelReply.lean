import Bilevel.ChiVirtualFrameIrrelevance
import Bilevel.ChiExtensionFullGradient

/-! Actual full lower-gradient replies from disclosed columns and a full
query. The inverse and every gradient are computed from the explicit virtual
scalar; no undisclosed frame enters the formula. -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory
namespace Bilevel.ChiPrefixEvaluation
open ChiRecursive ChiCarrier PrimitiveGeometry ChiExtension PartialLegendre
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

abbrev FullVirtualQuery (M : Node E) (D : Geometry F) (m s : ℕ) :=
  VirtualState M D × FullNormalVariables E (Blocks m F) (Normals s)

def fullQueryInverseInput {M : Node E} {D : Geometry F} {m s : ℕ}
    (p : FullVirtualQuery M D m s) : VirtualQuery M D m s := (p.1,(p.2.fst.fst,p.2.snd))

variable (active : Bool) (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ)
  (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) (c v : ℝ) (hc : 0<c)
  (hβ : 0<(D J []).width) (hv : 1≤v) (s : ℕ)
  (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ) (dn : ℝ)
  (hR : ∀ i : Fin J,0<R (i.val+1)) (hw : ∀ i : Fin J,0<(D (i.val+1) []).width)
  (h2 : ∀ p : {p : VirtualState M D | ValidState M D rM r p},∀ z,
    ‖iteratedFDeriv ℝ 2 (statePotential active m M D J rM r c v s index radialIndex fineIndex rad R dn p.1) z‖≤1/12)

def virtualFullGradient (μ L : ℝ) (p : FullVirtualQuery M D m s) :
    FullNormalVariables E (Blocks m F) (Normals s) :=
  let z := queryInverse active m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw h2
    (fullQueryInverseInput p)
  let a := (gradient (reassociate (statePotential active m M D J rM r c v s
    index radialIndex fineIndex rad R dn p.1)) (pack p.2.fst.fst z)).fst
  (3*μ/2) • normalConjugateProjection.adjoint (pack (-a) z)-
    (L/4) • bilinearCouplingOperator normalOuterProjection normalTangentProjection p.2

theorem virtualFullGradient_eq (μ L : ℝ) (p : FullVirtualQuery M D m s)
    (hp : ValidState M D rM r p.1) :
    virtualFullGradient active m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw h2 μ L p=
    gradient (fullExtensionLower (statePotential active m M D J rM r c v s index radialIndex fineIndex rad R dn p.1)
      (statePotential_contDiff active m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw p.1 hp)
      ⟨1/12,by norm_num⟩ (h2 ⟨p.1,hp⟩) (by change (1/12:ℝ)<1;norm_num) μ L) p.2 := by
  rw [(fullExtensionLower_hasGradientAt _ _ _ _ _ μ L p.2).gradient]
  unfold virtualFullGradient
  rw [queryInverse_eq_jointSolution active m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn
    hR hw h2 (fullQueryInverseInput p) hp]
  rfl

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
  [MeasurableSpace (Joint (Blocks m F) (Normals s))] [BorelSpace (Joint (Blocks m F) (Normals s))]
  [MeasurableSpace (Joint E (Joint (Blocks m F) (Normals s)))]
  [BorelSpace (Joint E (Joint (Blocks m F) (Normals s)))]
  [MeasurableSpace (FullNormalVariables E (Blocks m F) (Normals s))]
  [BorelSpace (FullNormalVariables E (Blocks m F) (Normals s))]

include h2 in
theorem virtualFullGradient_measurable (μ L : ℝ) :
    Measurable (virtualFullGradient active m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw h2 μ L) := by
  let V := Joint (Blocks m F) (Normals s)
  let W := Joint E V
  let Q := FullNormalVariables E (Blocks m F) (Normals s)
  letI : SecondCountableTopology (Blocks m F) := inferInstance
  letI : SecondCountableTopology (Joint E (Blocks m F)) := inferInstance
  letI : SecondCountableTopology V := inferInstance
  letI : SecondCountableTopology W := inferInstance
  letI : SecondCountableTopology Q :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Joint E (Blocks m F)) V).toHomeomorph.secondCountableTopology
  letI : BorelSpace (VirtualState M D) := inferInstance
  letI : SecondCountableTopology (VirtualState M D) := inferInstance
  letI : OpensMeasurableSpace (VirtualState M D) := inferInstance
  have hmacro : Measurable (fun p : FullVirtualQuery M D m s => p.2.fst.fst) :=
    ((jointFstLinear.comp jointFstLinear : Q →L[ℝ] E).continuous.measurable).comp measurable_snd
  have hlower : Measurable (fun p : FullVirtualQuery M D m s => p.2.snd) :=
    ((jointSndLinear : Q →L[ℝ] V).continuous.measurable).comp measurable_snd
  have hinput : Measurable (fullQueryInverseInput (M:=M) (D:=D) (m:=m) (s:=s)) :=
    measurable_fst.prodMk (hmacro.prodMk hlower)
  let inv := queryInverse active m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw h2
  have hinv := (queryInverse_measurable active m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw h2).comp hinput
  let pull : VirtualState M D × W → VirtualState M D × Full (Joint E (Blocks m F)) s :=
    fun p => (p.1,associateLeft p.2)
  have hpull : Continuous pull := continuous_fst.prodMk (associateLeft.continuous.comp continuous_snd)
  have hscalar := (statePotential_continuous active m M D J rM r c v s index radialIndex fineIndex rad R dn).comp hpull
  have hgrad := ParametricGradient.gradient_measurable
    (fun p : VirtualState M D => reassociate (statePotential active m M D J rM r c v s index radialIndex fineIndex rad R dn p)) hscalar
  have hpoint : Measurable (fun p : FullVirtualQuery M D m s => pack p.2.fst.fst (inv (fullQueryInverseInput p))) :=
    (packLinear (X:=E) (Y:=V)).continuous.measurable.comp (hmacro.prodMk hinv)
  have heval := hgrad.comp (measurable_fst.prodMk hpoint)
  have hfirst := (jointFstLinear : W →L[ℝ] E).continuous.measurable.comp heval
  have hpair := (packLinear (X:=E) (Y:=V)).continuous.measurable.comp (hfirst.neg.prodMk hinv)
  have hconj := (normalConjugateProjection.adjoint : W →L[ℝ] Q).continuous.measurable.comp hpair
  let A : Q →L[ℝ] Blocks m F := normalOuterProjection
  let B : Q →L[ℝ] Blocks m F := normalTangentProjection
  have hcoup := (bilinearCouplingOperator A B).continuous.measurable.comp
    (measurable_snd : Measurable (Prod.snd : FullVirtualQuery M D m s → Q))
  exact (hconj.const_smul (3*μ/2)).sub (hcoup.const_smul (L/4))

end Bilevel.ChiPrefixEvaluation
