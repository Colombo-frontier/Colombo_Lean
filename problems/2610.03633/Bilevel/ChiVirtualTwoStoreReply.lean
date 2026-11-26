import Bilevel.ChiVirtualSampleReply

/-! Observable source execution uses the old store for the inactive branch
and the newly disclosed store for the successful branch. Only a true coin
requires active-branch agreement with the original fixed oracle. -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory
namespace Bilevel.ChiPrefixEvaluation
open ChiRecursive ChiCarrier PrimitiveGeometry ChiExtension PartialLegendre
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

abbrev TwoStoreQuery (M : Node E) (D : Geometry F) (m s : ℕ) :=
  (VirtualState M D × VirtualState M D) × FullNormalVariables E (Blocks m F) (Normals s)

variable (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ)
  (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) (c v : ℝ) (hc : 0<c)
  (hβ : 0<(D J []).width) (hv : 1≤v) (s : ℕ)
  (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ) (dn : ℝ)
  (hR : ∀ i : Fin J,0<R (i.val+1)) (hw : ∀ i : Fin J,0<(D (i.val+1) []).width)
  (h2 : ∀ active : Bool,∀ p : {p : VirtualState M D | ValidState M D rM r p},∀ z,
    ‖iteratedFDeriv ℝ 2 (statePotential active m M D J rM r c v s index radialIndex fineIndex rad R dn p.1) z‖≤1/12)

def virtualTwoStoreSample (μ L π : ℝ) (coin : Bool) (p : TwoStoreQuery M D m s) :
    FullNormalVariables E (Blocks m F) (Normals s) :=
  let g₀ := virtualFullGradient false m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw (h2 false) μ L (p.1.1,p.2)
  let g := virtualFullGradient true m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw (h2 true) μ L (p.1.2,p.2)
  BernoulliOracle.sample π g₀ (g-g₀) coin

theorem virtualTwoStoreSample_eq_original (μ L π : ℝ) (coin : Bool) (p : TwoStoreQuery M D m s)
    (g g₀ : FullNormalVariables E (Blocks m F) (Normals s) → ℝ)
    (hzero : virtualFullGradient false m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw
      (h2 false) μ L (p.1.1,p.2)=gradient g₀ p.2)
    (hone : coin=true → virtualFullGradient true m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw
      (h2 true) μ L (p.1.2,p.2)=gradient g p.2) :
    virtualTwoStoreSample m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw h2 μ L π coin p=
      ChiConservative.sampleGradient g g₀ π coin p.2 := by
  cases coin with
  | false => simp only [virtualTwoStoreSample,ChiConservative.sampleGradient,BernoulliOracle.sample,
      Bool.false_eq_true,if_false,zero_smul,add_zero,hzero]
  | true => simp only [virtualTwoStoreSample,ChiConservative.sampleGradient,hzero,hone rfl]

theorem virtualTwoStoreSample_same_store (μ L π : ℝ) (coin : Bool) (p : FullVirtualQuery M D m s) :
    virtualTwoStoreSample m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw h2 μ L π coin ((p.1,p.1),p.2)=
      virtualSampleGradient m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw h2 μ L π coin p := rfl

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
  [MeasurableSpace (Joint (Blocks m F) (Normals s))] [BorelSpace (Joint (Blocks m F) (Normals s))]
  [MeasurableSpace (Joint E (Joint (Blocks m F) (Normals s)))]
  [BorelSpace (Joint E (Joint (Blocks m F) (Normals s)))]
  [MeasurableSpace (FullNormalVariables E (Blocks m F) (Normals s))]
  [BorelSpace (FullNormalVariables E (Blocks m F) (Normals s))]

theorem virtualTwoStoreSample_measurable (μ L π : ℝ) :
    Measurable (fun p : TwoStoreQuery M D m s × Bool =>
      virtualTwoStoreSample m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw h2 μ L π p.2 p.1) := by
  let Q := FullNormalVariables E (Blocks m F) (Normals s)
  let V := Joint (Blocks m F) (Normals s)
  letI : SecondCountableTopology V := inferInstance
  letI : SecondCountableTopology (Joint E (Blocks m F)) := inferInstance
  letI : SecondCountableTopology Q :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Joint E (Blocks m F)) V).toHomeomorph.secondCountableTopology
  have hold : Measurable (fun p : TwoStoreQuery M D m s × Bool => (p.1.1.1,p.1.2)) :=
    measurable_fst.fst.fst.prodMk measurable_fst.snd
  have hnew : Measurable (fun p : TwoStoreQuery M D m s × Bool => (p.1.1.2,p.1.2)) :=
    measurable_fst.fst.snd.prodMk measurable_fst.snd
  have hzero := (virtualFullGradient_measurable false m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw (h2 false) μ L).comp hold
  have hone := (virtualFullGradient_measurable true m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw (h2 true) μ L).comp hnew
  have hcoin : Measurable (fun p : TwoStoreQuery M D m s × Bool => if p.2 then π⁻¹ else (0:ℝ)) :=
    (measurable_of_finite (fun b : Bool => if b then π⁻¹ else (0:ℝ))).comp measurable_snd
  exact hzero.add (hcoin.smul (hone.sub hzero))

end Bilevel.ChiPrefixEvaluation
