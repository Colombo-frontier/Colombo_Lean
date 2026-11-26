import Bilevel.TransportQuadraticObserved
import Bilevel.TransportQuadraticOriginal
import Bilevel.TransportQuadraticSourceCertificate

/-! Complete original reply equality on the measured event of the literal
compiled execution. There is no independent prefix, projection, locality,
or local-reply premise: these follow from the SAME run and public cap. -/
noncomputable section
open MeasureTheory
universe u v
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiExtensionCalibration
  ChiHierarchyExecution EndpointTransportResponse TransportRound TransportNetwork
  PrimitiveGeometry PartialLegendre TransportAugmented
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem quadraticObserved_reply {C : Type u} {S : Type v} [MeasurableSpace C] [MeasurableSpace S]
    (macroN n D : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
    (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
    (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) 0,chainSize i+1≤D)
    (hT : capacity (sourceCounts macroN cn ratios resolutions) 1 0≤D)
    (hA : auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) 0+1≤D)
    (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km ν ρ R δ c : ℝ)
    [MeasurableSpace (Physical n D)] [BorelSpace (Physical n D)]
    [MeasurableSpace (QuadraticOutput D)] [BorelSpace (QuadraticOutput D)]
    [MeasurableSpace (QuadraticQuery n D)] [BorelSpace (QuadraticQuery n D)]
    (P : BorelAdaptive.Program S (QuadraticQuery n D) (QuadraticReply n D) (QuadraticOutput D))
    (start : C → S) (hl : 0< initial.curvature) (hw : 0< initial.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hη1 : ∀ j,resolutions j≤1)
    (hweight : ∀ j,0<weight j) (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km)
    (τ : ℝ) (hτ : 0<τ) (N t : ℕ) (ht : t<N)
    (s : C × PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D)
    (hobs : quadraticObserved macroN n D cn ratios resolutions hdim hAll hT hA initial weight
      A Kminus ζ CR Km ν ρ R δ c P start τ N s) :
    let st := quadraticRun macroN n D cn ratios resolutions hdim hAll hT hA initial weight
      A Kminus ζ CR Km ν ρ R δ c P start s t
    let w := P.query st.1.2.2.1
    quadraticEvaluate macroN n D cn ratios resolutions hdim hAll hT initial weight
      A Kminus ζ CR Km ν ρ R δ c t
      (w,(st.1.2.2.2,(st.2,batch (augment st.2 (quadraticNetworkQueries w)) s.2.1)))=
      quadraticOriginalReply macroN n D cn ratios resolutions hdim hAll hT initial weight
        A Kminus ζ CR Km ν ρ R δ c s.2 w := by
  let counts := sourceCounts macroN cn ratios resolutions
  let schedule := auxiliaryRoundSchedule counts 0 (n+1) (Nat.succ_pos n)
  let ctl := quadraticController (C:=C) macroN n D cn ratios resolutions hdim hAll hT initial weight
    A Kminus ζ CR Km ν ρ R δ c P
  let st := quadraticRun macroN n D cn ratios resolutions hdim hAll hT hA initial weight
    A Kminus ζ CR Km ν ρ R δ c P start s t
  let w := P.query st.1.2.2.1
  let WM := analyticalAuxSpaceAny ctl t (st.1.2,st.2)
  have qi := quadraticRun_query_membership macroN n D cn ratios resolutions hdim hAll hT hA initial weight
    A Kminus ζ CR Km ν ρ R δ c P start s t
  have hE := quadraticObserved_energy macroN n D cn ratios resolutions hdim hAll hT hA initial weight
    A Kminus ζ CR Km ν ρ R δ c P start τ N t ht s hobs
  have hgerm := sourceQuadratic_prefix_germ macroN n D 1 cn ratios resolutions hdim hAll hT hA s.2
    (networkChoose ctl) (networkRespond schedule ctl) (initialMemoryAny hA start (s.1,s.2.2))
    initial weight A Kminus ζ CR Km hl hw hr hη hη1 hweight hζ hCR hKm ν ρ R τ hτ N t ht
    WM (quadraticUpperProjection n D w) qi.1 qi.2 hE hobs.1.1
  have hpfx := quadraticRun_prefix macroN n D cn ratios resolutions hdim hAll hT hA initial weight
    A Kminus ζ CR Km ν ρ R δ c P start s t
  dsimp only
  rw [hpfx]
  exact quadraticEvaluate_eq_original_of_germ macroN n D cn ratios resolutions hdim hAll hT initial weight
    A Kminus ζ CR Km ν ρ R δ c s.2 t _ st.2 w hgerm

end Bilevel.TransportHierarchy
