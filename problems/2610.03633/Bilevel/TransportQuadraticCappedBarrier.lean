import Bilevel.TransportQuadraticSeedEvent
import Bilevel.TransportQuadraticCoupling
import Bilevel.TransportQuadraticTerminal

/-! The actual original capped output inherits the same-run terminal
barrier. The supplied deterministic scalar barrier is the construction's
analytic gradient barrier, not an information or probability assumption. -/
noncomputable section
open MeasureTheory
universe u v
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiExtensionCalibration
  ChiHierarchyExecution EndpointTransportResponse TransportRound TransportNetwork
  PrimitiveGeometry PartialLegendre TransportAugmented
set_option autoImplicit false
set_option maxHeartbeats 1500000

variable {C : Type u} {S : Type v} [MeasurableSpace C] [MeasurableSpace S]
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
  (start : C → S)

theorem quadraticCapped_barrier
    (hl : 0< initial.curvature) (hw : 0< initial.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hη1 : ∀ j,resolutions j≤1)
    (hweight : ∀ j,0<weight j) (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km)
    (τ ε : ℝ) (hτ : 0<τ) (N : ℕ)
    (hN : N<(n+1)*capacity (sourceCounts macroN cn ratios resolutions) 1 0)
    (loss : PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D × QuadraticOutput D → ℝ)
    (hbarrier : ∀ s x,
      (sourcePhysicalMacro macroN 0 n D cn ratios resolutions hAll s initial Km).coordinates x.fst (Fin.last macroN)< initial.width →
      8*ε≤loss (s,x))
    (z : BorelAdaptive.Sample (PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D) C Unit)
    (hg : quadraticSeedGood macroN n D cn ratios resolutions hdim hAll hT hA initial weight
      A Kminus ζ CR Km ν ρ R δ c P start τ N z) :
    8*ε≤loss (BorelAdaptive.seededCapped P
      (fun sample query (_ : Unit) => quadraticOriginalReply macroN n D cn ratios resolutions hdim hAll hT
        initial weight A Kminus ζ CR Km ν ρ R δ c sample query) start N z) := by
  have he := quadraticObserved_state_eq_original macroN n D cn ratios resolutions hdim hAll hT hA initial weight
    A Kminus ζ CR Km ν ρ R δ c P (fun q : C × (ℕ → Unit) => start q.1)
    hl hw hr hη hη1 hweight hζ hCR hKm τ hτ N N le_rfl (z.2,z.1) hg
  have hb := quadraticObserved_terminal macroN n D cn ratios resolutions hdim hAll hT hA initial weight
    A Kminus ζ CR Km ν ρ R δ c P (fun q : C × (ℕ → Unit) => start q.1)
    hl hw hr hη hweight hζ hCR hKm τ hτ N hN (z.2,z.1) hg
  dsimp only at he hb
  rw [he] at hb
  have hdraw : z.2.2=(fun _ => ()) := Subsingleton.elim _ _
  apply hbarrier z.1
  simpa only [BorelAdaptive.seededCapped,BorelAdaptive.seedInput,BorelAdaptive.cappedOutput,hdraw] using hb

end Bilevel.TransportHierarchy
