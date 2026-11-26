import Bilevel.TransportPhysicalFullDisclosure
import Bilevel.TransportHierarchyFullDisclosure
import Bilevel.EndpointTransportVirtualJointExact

/-! Named original physical scalar and full-SFO reply on the one sampled
network/auxiliary family. The lower scalar is the actual hybrid partial
conjugate; no prescribed support or virtual oracle is part of this definition. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiExtensionCalibration
  EndpointTransportResponse TransportRound TransportNetwork PrimitiveGeometry PartialLegendre ChiExtension ChiPrefixEvaluation
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable (macroN J n D s : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤D)
  (hT : capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0≤D)
  (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km ν : ℝ) (fine : ChiFine.Parameters)
  (index radialIndex : Fin J → Fin s) (fineIndex : Fin s)
  (ρ R : ℕ → ℝ) (dn : ℝ) (b : Normals s) (m δ c₀ cend : ℝ)


variable (hl : 0 < initial.curvature) (hw : 0 < initial.width)
  (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hη1 : ∀ j,resolutions j≤1)
  (hweight : ∀ j,0<weight j) (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km)


section Measurable
variable [MeasurableSpace (Physical n D)] [BorelSpace (Physical n D)]
  [MeasurableSpace (PhysicalQuery J n D s)] [BorelSpace (PhysicalQuery J n D s)]
  (hℓ : ∀ sample : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D,
    fine.ℓ=(sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT sample initial weight A Kminus ζ CR J []).ell)
  (hβ : ∀ sample : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D,
    fine.β=(sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT sample initial weight A Kminus ζ CR J []).width)

include hl hw hr hη hη1 hweight hζ hCR hKm hℓ hβ in
theorem physicalOriginalPotentialGradient_measurable :
    Measurable (fun p : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D × PhysicalQuery J n D s =>
      gradient (physicalOriginalPotential macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km fine index radialIndex fineIndex ρ R dn p.1) p.2) := by
  let Z := PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D × PhysicalQuery J n D s
  have hd := (completeHierarchyData_measurable hdim hAll hT).comp
    (measurable_fst : Measurable (fun p : Z => p.1))
  have hm := (statePhysicalExtension_gradient_measurable
    (sourcePhysicalMacro macroN J n D cn ratios resolutions hAll
      (templateSample (sourceCounts macroN cn ratios resolutions) J n D) initial Km)
    (sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT
      (templateSample (sourceCounts macroN cn ratios resolutions) J n D) initial weight A Kminus ζ CR)
    fine index radialIndex fineIndex ρ R dn
    (fun _ => macroN+1) (fun _ j _ => sourceChainIndex cn (ratios j) (resolutions j)+1)
    (fun _ j _ => sourceChainIndex cn (ratios j) (resolutions j)+1)).comp
      (((measurable_const : Measurable (fun _ : Z => (0 : ℕ))).prodMk hd).prodMk measurable_snd)
  convert hm using 1
  funext p
  rw [physicalOriginalPotential_full macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km fine index radialIndex fineIndex ρ R dn hl hw hr hη hη1 hweight hζ hCR hKm p.1 (hℓ p.1) (hβ p.1)]
  rfl

include hl hw hr hη hη1 hweight hζ hCR hKm in
theorem physicalOriginalUpperGradient_measurable (hJ : 0<J) :
    Measurable (fun p : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D × PhysicalQuery J n D s =>
      gradient (physicalOriginalUpper macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν ρ R b p.1) p.2) := by
  let Z := PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D × PhysicalQuery J n D s
  have hd := (completeHierarchyData_measurable hdim hAll hT).comp
    (measurable_fst : Measurable (fun p : Z => p.1))
  have hm := (statePhysicalUpper_gradient_measurable
    (sourcePhysicalMacro macroN J n D cn ratios resolutions hAll
      (templateSample (sourceCounts macroN cn ratios resolutions) J n D) initial Km) ν
    (sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT
      (templateSample (sourceCounts macroN cn ratios resolutions) J n D) initial weight A Kminus ζ CR)
    (ρ 0) (R 0) b
    (fun _ => macroN+1) (fun _ j _ => sourceChainIndex cn (ratios j) (resolutions j)+1)).comp
      (((measurable_const : Measurable (fun _ : Z => (0 : ℕ))).prodMk hd).prodMk measurable_snd)
  convert hm using 1
  funext p
  rw [physicalOriginalUpper_full macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν ρ R b hl hw hr hη hη1 hweight hζ hCR hKm hJ p.1]
  rfl

variable (K : NNReal) (hK : K<1)
  (hF : ∀ sample : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D,
    LipschitzWith K (gradient (physicalOriginalPotential macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km fine index radialIndex fineIndex ρ R dn sample)))

include hl hw hr hη hη1 hweight hζ hCR hKm hℓ hβ in
theorem physicalOriginalLowerGradient_measurable
    (hreg : ∀ sample : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D,
      ContDiff ℝ 3 (physicalOriginalPotential macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km fine index radialIndex fineIndex ρ R dn sample)) :
    Measurable (fun p : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D × PhysicalQuery J n D s =>
      gradient (physicalOriginalLower macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km fine index radialIndex fineIndex ρ R dn m δ c₀ cend K hK hF p.1) p.2) := by
  letI : SecondCountableTopology (Blocks J (Block D)) := inferInstance
  letI : SecondCountableTopology (Physical n D) := inferInstance
  letI : SecondCountableTopology (HybridTangent (Blocks J (Block D)) n D) := inferInstance
  letI : SecondCountableTopology (Normals s) := inferInstance
  letI : SecondCountableTopology (HybridVariables (Blocks J (Block D)) (Normals s) n D) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (HybridTangent (Blocks J (Block D)) n D) (Normals s)).toHomeomorph.secondCountableTopology
  letI : SecondCountableTopology (PhysicalOutput J D) := inferInstance
  letI : SecondCountableTopology (PhysicalQuery J n D s) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (PhysicalOutput J D)
      (HybridVariables (Blocks J (Block D)) (Normals s) n D)).toHomeomorph.secondCountableTopology
  let Z := PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D × PhysicalQuery J n D s
  let F := physicalOriginalPotential macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km fine index radialIndex fineIndex ρ R dn
  let G := fun sample => gradient (F sample)
  have hG : Measurable (fun z : Z => G z.1 z.2) :=
    physicalOriginalPotentialGradient_measurable macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km fine index radialIndex fineIndex ρ R dn hl hw hr hη hη1 hweight hζ hCR hKm hℓ hβ
  let g : Generators (n+1) D 0 := fun _ _ => 0
  have hq : Measurable (fun p : Z => physicalNetworkQueries p.2) := physicalNetworkQueries_measurable.comp measurable_snd
  have hz : Measurable (fun p : Z => p.1.1) := measurable_fst.comp measurable_fst
  have hb := (batch_joint_measurable (n+1) D (0+1)).comp
    (((augment_measurable (n+1) D 0 1).comp
      ((measurable_const : Measurable (fun _ : Z => g)).prodMk hq)).prodMk hz)
  have hm := (virtualHybridReply_measurable (a:=0) G hG m δ c₀ cend (0 : Fin 1)).comp
    ((measurable_id : Measurable (fun p : Z => p)).prodMk (hq.prodMk hb))
  convert hm using 1
  funext p
  exact (virtualHybridReply_actual G p.1 hK (hF p.1) (F p.1)
    (fun w => ((hreg p.1).differentiable (by norm_num) w).hasGradientAt)
    m δ c₀ cend p.1.1 g (physicalNetworkQueries p.2) (0 : Fin 1) p.2
    (physicalNetworkQueries_physical p.2)).symm

include hl hw hr hη hη1 hweight hζ hCR hKm hℓ hβ in
theorem physicalOriginalReply_measurable (hJ : 0<J)
    (hreg : ∀ sample : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D,
      ContDiff ℝ 3 (physicalOriginalPotential macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km fine index radialIndex fineIndex ρ R dn sample)) :
    Measurable (fun p : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D × PhysicalQuery J n D s =>
      physicalOriginalReply macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend K hK hF p.1 p.2) :=
  (physicalOriginalUpperGradient_measurable macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν ρ R b hl hw hr hη hη1 hweight hζ hCR hKm hJ).prodMk
    (physicalOriginalLowerGradient_measurable macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km fine index radialIndex fineIndex ρ R dn m δ c₀ cend hl hw hr hη hη1 hweight hζ hCR hKm hℓ hβ K hK hF hreg)

end Measurable
end Bilevel.TransportHierarchy
