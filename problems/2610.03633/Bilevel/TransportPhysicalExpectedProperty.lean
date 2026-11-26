import Bilevel.TransportPhysicalExpected
import Bilevel.TransportPhysicalLoss
import Bilevel.TransportPhysicalOriginal
import Bilevel.TransportHierarchyStoreHessian
import Bilevel.EndpointTransportVirtualJointExact

/-! The public uniform core certificate specializes to the actual physical
source family and yields its global contraction. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiExtensionCalibration
  EndpointTransportResponse TransportRound TransportNetwork PrimitiveGeometry PartialLegendre ChiExtension BorelAdaptive
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable (macroN J n D s : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤D)
  (hT : capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0≤D)
  (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km ν : ℝ) (fine : ChiFine.Parameters)
  (index radialIndex : Fin J → Fin s) (fineIndex : Fin s)
  (ρ R : ℕ → ℝ) (dn : ℝ) (b : Normals s) (m δ c₀ cend : ℝ)

variable
  (hF : ∀ sample : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D,
    LipschitzWith (⟨1/12,by norm_num⟩ : NNReal) (gradient (physicalOriginalPotential macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km fine index radialIndex fineIndex ρ R dn sample)))
  (K ε : ℝ)

def PhysicalBarrier : Prop :=
  ∀ (sample : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D) (x : PhysicalOutput J D),
    (sourcePhysicalMacro macroN J n D cn ratios resolutions hAll sample initial Km).coordinates x.fst.fst (Fin.last macroN) < initial.width →
    8*ε≤physicalOriginalLoss macroN J n D cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν ρ R K sample x

def PhysicalRateProperty (bound : ℝ) : Prop :=
  ∀ [MeasurableSpace (Physical n D)] [BorelSpace (Physical n D)]
    [MeasurableSpace (PhysicalOutput J D)] [BorelSpace (PhysicalOutput J D)]
    [MeasurableSpace (PhysicalQuery J n D s)] [BorelSpace (PhysicalQuery J n D s)],
  ∀ {Private State : Type} [MeasurableSpace Private] [MeasurableSpace State]
    (alg : Program State (PhysicalQuery J n D s) (PhysicalReply J n D s) (PhysicalOutput J D))
    (start : Private → State) (_hstart : Measurable start) (σ : Measure Private) [IsProbabilityMeasure σ]
    (_haccuracy : ∀ sample : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D,
      (∫⁻ z,ENNReal.ofReal (Function.uncurry (physicalOriginalLoss macroN J n D cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν ρ R K)
        (seededStopped alg (fun a q (_ : Unit) => physicalOriginalReply macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend
          ⟨1/12,by norm_num⟩ (by change (1:ℝ)/12<1;norm_num) hF a q) start (sample,z)))
        ∂σ.prod (Measure.dirac (fun _ : ℕ => ())))≤ENNReal.ofReal ε),
    ∃ sample : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D,
      ENNReal.ofReal bound≤∫⁻ z,seededCalls alg
        (fun a q (_ : Unit) => physicalOriginalReply macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend ⟨1/12,by norm_num⟩
          (by change (1:ℝ)/12<1;norm_num) hF a q) start (sample,z)
        ∂σ.prod (Measure.dirac (fun _ : ℕ => ()))

abbrev PhysicalExpectedProperty : Prop :=
  PhysicalRateProperty macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend hF K ε
    (((n+1)*capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0:ℕ)/512)

variable
    (hcomplete : ∀ (dim' : ℕ) (Q : Rotations n dim')
      (U : Space macroN →ₗᵢ[ℝ] Block dim')
      (V : ∀ j,List ℕ → Space (sourceChainIndex cn (ratios j) (resolutions j)) →ₗᵢ[ℝ] Block dim'),
      let M' := ChiOuter.sourceMacroNode macroN initial Km U
      let G' := sourceGeometry initial ratios resolutions weight A Kminus ζ cn CR V
      let rad' := fun j => weight j*(G' j []).nu
      let R' := fun j => (G' j []).radius
      ContDiff ℝ 3 (physicalHierarchyExtension Q M' G' fine J s index radialIndex fineIndex rad' R' dn) ∧
      ∀ z,‖iteratedFDeriv ℝ 2 (physicalHierarchyExtension Q M' G' fine J s index radialIndex fineIndex rad' R' dn) z‖≤(1:ℝ)/12)
    (hρ : ∀ (sample : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D) j,
      ρ j=weight j*(sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT sample initial weight A Kminus ζ CR j []).nu)
    (hR : ∀ (sample : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D) j,
      R j=(sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT sample initial weight A Kminus ζ CR j []).radius)
    (hℓ : ∀ sample : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D,
      fine.ℓ=(sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT sample initial weight A Kminus ζ CR J []).ell)
    (hβ : ∀ sample : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D,
      fine.β=(sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT sample initial weight A Kminus ζ CR J []).width)
    (hJ : 0<J)
    (hl : 0 < initial.curvature) (hw : 0 < initial.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hη1 : ∀ j,resolutions j≤1)
    (hweight : ∀ j,0<weight j) (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km)

include hcomplete hρ hR hℓ hβ hJ hl hw hr hη hη1 hweight hζ hCR hKm in
theorem physical_expected_property
    (hA : auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) J+1≤D)
    (τ : ℝ) (hτ : 0<τ) (hε : 0<ε)
    (hbudget : ∀ N : ℕ,N≤(n+1)*capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0 →
      physicalBudget macroN J n D cn ratios resolutions initial weight CR ζ Km τ (1/8) N)
    (hbarrier : PhysicalBarrier macroN J n D cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν ρ R K ε) :
    PhysicalExpectedProperty macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend hF K ε := by
  intro instMP instBP instMO instBO instMQ instBQ Private State instP instS alg start hstart σ instσ haccuracy
  exact physical_expected_queries macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight
    A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend alg start
    hcomplete hρ hR hF hℓ hβ hJ hl hw hr hη hη1 hweight hζ hCR hKm
    (σ.prod (Measure.dirac (fun _ : ℕ => ()))) hstart τ ε hτ hε
    (Function.uncurry (physicalOriginalLoss macroN J n D cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν ρ R K))
    (physicalOriginalLoss_measurable macroN J n D cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν ρ R K) (fun _ => norm_nonneg _) hbarrier hbudget haccuracy

theorem PhysicalRateProperty.mono {aBound bBound : ℝ} (hab : aBound≤bBound)
    (h : PhysicalRateProperty macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend hF K ε bBound) : PhysicalRateProperty macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend hF K ε aBound := by
  intro instMP instBP instMO instBO instMQ instBQ Private State instP instS alg start hstart σ instσ haccuracy
  obtain ⟨sample,hs⟩ := @h instMP instBP instMO instBO instMQ instBQ Private State instP instS
    alg start hstart σ instσ haccuracy
  exact ⟨sample,(ENNReal.ofReal_le_ofReal hab).trans hs⟩

end Bilevel.TransportHierarchy
