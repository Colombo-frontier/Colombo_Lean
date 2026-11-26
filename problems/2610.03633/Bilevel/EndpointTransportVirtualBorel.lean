import Bilevel.EndpointTransportVirtualOuterContinuity
import Bilevel.TransportVirtualHybridReply

/-! A total Borel lower-reply evaluator on all disclosed arrays. Its
partial-conjugate input is fixed before the frozen edge batch; the only
batch-dependent term is the public physical Hessian correction. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open MeasureTheory
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre ChiBoundedChain ChiRecursive ChiCarrier ChiPrefixEvaluation ChiExtension
  TransportHierarchy TransportRound TransportNetwork
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def statePhysicalExtension {J n D s : ℕ} (M : Node E) (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (ρ R : ℕ → ℝ) (dn : ℝ)
    (rM : ℕ → ℕ) (r rs : ℕ → ℕ → List ℕ → ℕ) (data : PhysicalPrefixState M G n) :
    HybridQuery E (Blocks J (Block D)) (Normals s) n D → ℝ :=
  physicalExtension (statePhysicalPotential M G P index radialIndex fineIndex ρ R dn rM r rs data)

theorem statePhysicalExtension_continuous {J n D s : ℕ}
    (M : Node E) (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (ρ R : ℕ → ℝ) (dn : ℝ)
    (rM : ℕ → ℕ) (r rs : ℕ → ℕ → List ℕ → ℕ) :
    Continuous (Function.uncurry (statePhysicalExtension (n:=n) M G P index radialIndex fineIndex ρ R dn rM r rs)) := by
  have h := (statePhysicalPotential_continuous (n:=n) M G P index radialIndex fineIndex ρ R dn rM r rs).comp
    (continuous_fst.prodMk ((normalCoordinates (E:=E) (U:=Blocks J (Block D))
      (T:=HybridTangent (Blocks J (Block D)) n D) (V:=Normals s) (D:=D)).continuous.comp continuous_snd))
  exact h

section Measurable
variable [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {J n D s a p : ℕ}
  [MeasurableSpace (Physical n D)] [BorelSpace (Physical n D)]
  [MeasurableSpace (HybridQuery E (Blocks J (Block D)) (Normals s) n D)]
  [BorelSpace (HybridQuery E (Blocks J (Block D)) (Normals s) n D)]

theorem statePhysicalExtension_gradient_measurable
    (M : Node E) (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (ρ R : ℕ → ℝ) (dn : ℝ)
    (rM : ℕ → ℕ) (r rs : ℕ → ℕ → List ℕ → ℕ) :
    Measurable (fun z : PhysicalPrefixState M G n × HybridQuery E (Blocks J (Block D)) (Normals s) n D =>
      gradient (statePhysicalExtension M G P index radialIndex fineIndex ρ R dn rM r rs z.1) z.2) := by
  letI : SecondCountableTopology (Physical n D) := inferInstance
  letI : SecondCountableTopology (Block D) := inferInstance
  letI : SecondCountableTopology (ColumnData G) := inferInstance
  letI : SecondCountableTopology (EndpointColumnData G n) := inferInstance
  letI : BorelSpace (ColumnData G) := inferInstance
  letI : BorelSpace (EndpointColumnData G n) := inferInstance
  letI : SecondCountableTopology (PhysicalColumnData G n) := inferInstance
  letI : BorelSpace (PhysicalColumnData G n) := inferInstance
  letI : SecondCountableTopology (PhysicalPrefixData M G n) := inferInstance
  letI : BorelSpace (PhysicalPrefixData M G n) := inferInstance
  letI : BorelSpace (PhysicalPrefixState M G n) := inferInstance
  exact ParametricGradient.gradient_measurable
    (statePhysicalExtension M G P index radialIndex fineIndex ρ R dn rM r rs)
    (statePhysicalExtension_continuous M G P index radialIndex fineIndex ρ R dn rM r rs)

def physicalPrefixLowerReply (M : Node E) (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (ρ R : ℕ → ℝ) (dn : ℝ)
    (rM : ℕ → ℕ) (r rs : ℕ → ℕ → List ℕ → ℕ) (m δ c₀ cend : ℝ) (i : Fin p) :=
  virtualHybridReply (a:=a)
    (fun data => gradient (statePhysicalExtension (n:=n) M G P index radialIndex fineIndex ρ R dn rM r rs data))
    m δ c₀ cend i

theorem physicalPrefixLowerReply_measurable
    (M : Node E) (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (ρ R : ℕ → ℝ) (dn : ℝ)
    (rM : ℕ → ℕ) (r rs : ℕ → ℕ → List ℕ → ℕ) (m δ c₀ cend : ℝ) (i : Fin p) :
    Measurable (physicalPrefixLowerReply (n:=n) (a:=a) M G P index radialIndex fineIndex ρ R dn rM r rs m δ c₀ cend i) := by
  letI : SecondCountableTopology (Blocks J (Block D)) := inferInstance
  letI : SecondCountableTopology (Physical n D) := inferInstance
  letI : SecondCountableTopology (HybridTangent (Blocks J (Block D)) n D) := inferInstance
  letI : SecondCountableTopology (Normals s) := inferInstance
  letI : SecondCountableTopology (HybridVariables (Blocks J (Block D)) (Normals s) n D) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (HybridTangent (Blocks J (Block D)) n D) (Normals s)).toHomeomorph.secondCountableTopology
  letI : SecondCountableTopology (HybridOuter E (Blocks J (Block D)) D) := inferInstance
  letI : SecondCountableTopology (HybridQuery E (Blocks J (Block D)) (Normals s) n D) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (HybridOuter E (Blocks J (Block D)) D)
      (HybridVariables (Blocks J (Block D)) (Normals s) n D)).toHomeomorph.secondCountableTopology
  exact virtualHybridReply_measurable _
    (statePhysicalExtension_gradient_measurable M G P index radialIndex fineIndex ρ R dn rM r rs)
    m δ c₀ cend i

end Measurable
end Bilevel.EndpointTransportResponse
