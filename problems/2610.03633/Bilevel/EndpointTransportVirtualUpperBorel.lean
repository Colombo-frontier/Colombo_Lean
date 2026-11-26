import Bilevel.EndpointTransportVirtualUpperContinuity
import Bilevel.EndpointTransportVirtualBorel
import Bilevel.EndpointTransportUpperGerm

/-! Total Borel full upper reply from old disclosed arrays, retaining the
entire nonlinear base and normal readout. Pairing it with the frozen-batch
hybrid evaluator gives a literal two-gradient query reply. -/
noncomputable section
open MeasureTheory
open scoped Topology
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre ChiBoundedChain ChiRecursive ChiCarrier ChiPrefixEvaluation ChiExtension
  TransportHierarchy TransportRound TransportNetwork
set_option autoImplicit false
set_option maxHeartbeats 800000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def statePhysicalUpper {J n D s : ℕ} (M : Node E) (ν : ℝ) (G : Geometry (Block D))
    (ρ R : ℝ) (b : Normals s) (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ)
    (data : PhysicalPrefixState M G n) : HybridQuery E (Blocks J (Block D)) (Normals s) n D → ℝ :=
  physicalUpper (statePhysicalUpperBase (m:=J) M ν G J ρ R rM r data) b

theorem statePhysicalUpper_continuous {J n D s : ℕ} (M : Node E) (ν : ℝ) (G : Geometry (Block D))
    (ρ R : ℝ) (b : Normals s) (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) :
    Continuous (Function.uncurry (statePhysicalUpper (J:=J) (n:=n) M ν G ρ R b rM r)) := by
  let A : HybridQuery E (Blocks J (Block D)) (Normals s) n D →L[ℝ] PhysicalBase E J n D :=
    jointFstLinear.comp normalCoordinates
  let B : HybridQuery E (Blocks J (Block D)) (Normals s) n D →L[ℝ] Normals s :=
    jointSndLinear.comp normalCoordinates
  have hb := (statePhysicalUpperBase_continuous (m:=J) (n:=n) M ν G J ρ R rM r).comp
    (continuous_fst.prodMk (A.continuous.comp continuous_snd))
  have hn := (InnerProductSpace.toDual ℝ (Normals s) b).continuous.comp
    (B.continuous.comp
      (continuous_snd : Continuous (Prod.snd : PhysicalPrefixState M G n ×
        HybridQuery E (Blocks J (Block D)) (Normals s) n D → _)))
  exact hb.add hn

theorem statePhysicalUpper_gradient_eq_actual_of_germ [CompleteSpace E]
    {J n D s : ℕ} (Q : Rotations n D) (M : Node E) (ν : ℝ) (G : Geometry (Block D))
    (ρ R : ℝ) (b : Normals s) (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ)
    (data : PhysicalPrefixState M G n) (w : HybridQuery E (Blocks J (Block D)) (Normals s) n D)
    (he : physicalUpperBase J Q M ν G J ρ R =ᶠ[𝓝 (pack w.fst.fst.fst w.snd.fst)]
      statePhysicalUpperBase (m:=J) M ν G J ρ R rM r data) :
    gradient (statePhysicalUpper M ν G ρ R b rM r data) w=
      gradient (physicalUpper (U:=Blocks J (Block D)) (D:=D) (physicalUpperBase J Q M ν G J ρ R) b) w :=
  (physicalUpper_gradient_eq_of_base_germ b w he).symm

section Measurable
variable [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {J n D s a p : ℕ}
  [MeasurableSpace (Physical n D)] [BorelSpace (Physical n D)]
  [MeasurableSpace (HybridQuery E (Blocks J (Block D)) (Normals s) n D)]
  [BorelSpace (HybridQuery E (Blocks J (Block D)) (Normals s) n D)]

theorem statePhysicalUpper_gradient_measurable (M : Node E) (ν : ℝ) (G : Geometry (Block D))
    (ρ R : ℝ) (b : Normals s) (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) :
    Measurable (fun z : PhysicalPrefixState M G n × HybridQuery E (Blocks J (Block D)) (Normals s) n D =>
      gradient (statePhysicalUpper M ν G ρ R b rM r z.1) z.2) := by
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
  exact ParametricGradient.gradient_measurable (statePhysicalUpper M ν G ρ R b rM r)
    (statePhysicalUpper_continuous (J:=J) (n:=n) M ν G ρ R b rM r)

def physicalPrefixJointReply (M : Node E) (ν : ℝ) (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (ρ R : ℕ → ℝ) (dn : ℝ) (b : Normals s)
    (rM : ℕ → ℕ) (r rs : ℕ → ℕ → List ℕ → ℕ) (m δ c₀ cend : ℝ) (i : Fin p) :=
  virtualJointReply (a:=a) (n:=n)
    (fun data => gradient (statePhysicalUpper M ν G (ρ 0) (R 0) b rM r data))
    (fun data => gradient (statePhysicalExtension M G P index radialIndex fineIndex ρ R dn rM r rs data))
    m δ c₀ cend i

theorem physicalPrefixJointReply_measurable (M : Node E) (ν : ℝ) (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (ρ R : ℕ → ℝ) (dn : ℝ) (b : Normals s)
    (rM : ℕ → ℕ) (r rs : ℕ → ℕ → List ℕ → ℕ) (m δ c₀ cend : ℝ) (i : Fin p) :
    Measurable (physicalPrefixJointReply (a:=a) (n:=n) M ν G P index radialIndex fineIndex ρ R dn b rM r rs m δ c₀ cend i) := by
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
  exact virtualJointReply_measurable _ _
    (statePhysicalUpper_gradient_measurable M ν G (ρ 0) (R 0) b rM r)
    (statePhysicalExtension_gradient_measurable M G P index radialIndex fineIndex ρ R dn rM r rs)
    m δ c₀ cend i
end Measurable

end Bilevel.EndpointTransportResponse
