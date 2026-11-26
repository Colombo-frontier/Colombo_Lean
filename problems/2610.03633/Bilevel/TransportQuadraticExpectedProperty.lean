import Bilevel.TransportQuadraticExpected
import Bilevel.TransportQuadraticOriginalLoss
import Bilevel.ChiCanonicalPublicData

/-! The actual deterministic transport expected-query property, with the
full original gradient pair and the named physical mean-gradient loss. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  ChiExtensionCalibration EndpointTransportResponse PrimitiveGeometry BorelAdaptive
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable (macroN n D : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) 0,chainSize i+1≤D)
  (hT : capacity (sourceCounts macroN cn ratios resolutions) 1 0≤D)
  (sc : Scale) (weight : ℕ → ℝ) (ζ CR Km : ℝ) (rad R : ℕ → ℝ) (K ε : ℝ)

def QuadraticBarrier : Prop :=
  ∀ (a : PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D) (x : QuadraticOutput D),
    (sourcePhysicalMacro macroN 0 n D cn ratios resolutions hAll a sc Km).coordinates x.fst (Fin.last macroN)<sc.width →
    8*ε≤quadraticOriginalLoss macroN n D cn ratios resolutions hdim hAll hT sc weight 3 1 ζ CR Km
      (sc.curvature/24) rad R K a x

def QuadraticRateProperty (δ c bound : ℝ) : Prop :=
  ∀ [MeasurableSpace (Physical n D)] [BorelSpace (Physical n D)]
    [MeasurableSpace (QuadraticOutput D)] [BorelSpace (QuadraticOutput D)]
    [MeasurableSpace (QuadraticQuery n D)] [BorelSpace (QuadraticQuery n D)],
  ∀ {Private State : Type} [MeasurableSpace Private] [MeasurableSpace State]
    (alg : Program State (QuadraticQuery n D) (QuadraticReply n D) (QuadraticOutput D))
    (start : Private → State) (_hstart : Measurable start) (σ : Measure Private) [IsProbabilityMeasure σ]
    (_haccuracy : ∀ a : PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D,
      (∫⁻ z,ENNReal.ofReal (Function.uncurry (quadraticOriginalLoss macroN n D cn ratios resolutions hdim hAll hT
        sc weight 3 1 ζ CR Km (sc.curvature/24) rad R K)
          (seededStopped alg (fun a q (_ : Unit) => quadraticOriginalReply macroN n D cn ratios resolutions hdim hAll hT
            sc weight 3 1 ζ CR Km (sc.curvature/24) (rad 0) (R 0) δ c a q) start (a,z)))
          ∂σ.prod (Measure.dirac (fun _ : ℕ => ())))≤ENNReal.ofReal ε),
    ∃ a : PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D,
      ENNReal.ofReal bound≤∫⁻ z,seededCalls alg
        (fun a q (_ : Unit) => quadraticOriginalReply macroN n D cn ratios resolutions hdim hAll hT
          sc weight 3 1 ζ CR Km (sc.curvature/24) (rad 0) (R 0) δ c a q) start (a,z)
          ∂σ.prod (Measure.dirac (fun _ : ℕ => ()))

abbrev QuadraticExpectedProperty (δ c : ℝ) : Prop :=
  QuadraticRateProperty macroN n D cn ratios resolutions hdim hAll hT sc weight ζ CR Km rad R K ε δ c
    (((n+1)*capacity (sourceCounts macroN cn ratios resolutions) 1 0:ℕ)/512)

theorem quadratic_expected_property
    (hA : auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) 0+1≤D)
    (hl : 0<sc.curvature) (hw : 0<sc.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hη1 : ∀ j,resolutions j≤1)
    (hweight : ∀ j,0<weight j) (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km)
    (δ c τ : ℝ) (hτ : 0<τ) (hε : 0<ε)
    (hbudget : ∀ N : ℕ,N≤(n+1)*capacity (sourceCounts macroN cn ratios resolutions) 1 0 →
      quadraticBudget macroN n D cn ratios resolutions sc weight CR ζ Km τ (1/8) N)
    (hbarrier : QuadraticBarrier macroN n D cn ratios resolutions hdim hAll hT sc weight ζ CR Km rad R K ε) :
    QuadraticExpectedProperty macroN n D cn ratios resolutions hdim hAll hT sc weight ζ CR Km rad R K ε δ c := by
  intro instMP instBP instMO instBO instMQ instBQ Private State instP instS alg start hstart σ instσ haccuracy
  exact quadratic_expected_queries macroN n D cn ratios resolutions hdim hAll hT hA sc weight 3 1 ζ CR Km
    (sc.curvature/24) (rad 0) (R 0) δ c alg start (σ.prod (Measure.dirac (fun _ : ℕ => ()))) hstart
    hl hw hr hη hη1 hweight hζ hCR hKm τ ε hτ hε
    (Function.uncurry (quadraticOriginalLoss macroN n D cn ratios resolutions hdim hAll hT sc weight 3 1 ζ CR Km
      (sc.curvature/24) rad R K))
    (quadraticOriginalLoss_measurable macroN n D cn ratios resolutions hdim hAll hT sc weight 3 1 ζ CR Km
      (sc.curvature/24) rad R K) (fun _ => norm_nonneg _) hbarrier hbudget haccuracy

theorem QuadraticRateProperty.mono {δ c a b : ℝ} (hab : a≤b)
    (h : QuadraticRateProperty macroN n D cn ratios resolutions hdim hAll hT sc weight ζ CR Km rad R K ε δ c b) :
    QuadraticRateProperty macroN n D cn ratios resolutions hdim hAll hT sc weight ζ CR Km rad R K ε δ c a := by
  intro instMP instBP instMO instBO instMQ instBQ Private State instP instS alg start hstart σ instσ haccuracy
  obtain ⟨s,hs⟩ := @h instMP instBP instMO instBO instMQ instBQ Private State instP instS
    alg start hstart σ instσ haccuracy
  exact ⟨s,(ENNReal.ofReal_le_ofReal hab).trans hs⟩

end Bilevel.TransportHierarchy
