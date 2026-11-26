import Bilevel.TransportQuadraticEvaluator
import Bilevel.TransportHierarchySourceReframe

/-! The evaluator is globally independent of its public template frame.
On a current-query source germ it equals the original complete upper and
lower gradients of the same sampled physical quadratic instance. -/
noncomputable section
open scoped Topology
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiExtensionCalibration
  EndpointTransportResponse TransportRound TransportNetwork PrimitiveGeometry PartialLegendre
set_option autoImplicit false
set_option maxHeartbeats 1300000

variable (macroN n D : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) 0,chainSize i+1≤D)
  (hT : capacity (sourceCounts macroN cn ratios resolutions) 1 0≤D)
  (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km ν ρ R δ c : ℝ)

def quadraticOriginalReply (s : PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D)
    (w : QuadraticQuery n D) : QuadraticReply n D :=
  (gradient (quadraticFullCore (physicalRotations s.1)
      (sourcePhysicalMacro macroN 0 n D cn ratios resolutions hAll s initial Km) ν
      (sourcePhysicalGeometry macroN 0 n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR) ρ R) w,
    gradient (ChiQuadratic.lower (physicalHessian δ (physicalRotations s.1))
      (endpointCoupling c (physicalRotations s.1))) w)

theorem quadraticEvaluate_template_independent
    (s : PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D) (t : ℕ)
    (z : TransportProgram.Input (QuadraticQuery n D) (n+1) D 1
      (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) 0))
      (auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) 0) t) :
    quadraticEvaluate macroN n D cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν ρ R δ c t z=
      prefixQuadraticJointReply (physicalRotations s.1)
        (sourcePhysicalMacro macroN 0 n D cn ratios resolutions hAll s initial Km) ν
        (sourcePhysicalGeometry macroN 0 n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR) ρ R
        (fun q => counter (sourceCounts macroN cn ratios resolutions) 1 q 0 [])
        (fun q i => canonicalCounter (sourceCounts macroN cn ratios resolutions) 0 q 0 [i.val]) δ c 0
        (((t/(n+1),quadraticSourceData macroN n D 1 t cn ratios resolutions z.2.1 z.2.2.1),z.1),
          (quadraticNetworkQueries z.1,z.2.2.2)) := by
  dsimp only [quadraticEvaluate]
  exact (prefixQuadraticJointReply_reframe (physicalRotations s.1)
    (fun _ => LinearIsometryEquiv.refl ℝ (Block D))
    (sourcePhysicalMacro macroN 0 n D cn ratios resolutions hAll
      (templateSample (sourceCounts macroN cn ratios resolutions) 0 n D) initial Km)
    (physicalMacroFrame hAll s) ν
    (sourcePhysicalGeometry macroN 0 n D cn ratios resolutions hdim hT
      (templateSample (sourceCounts macroN cn ratios resolutions) 0 n D) initial weight A Kminus ζ CR)
    (physicalFamily hdim hT s) ρ R
    (fun q => counter (sourceCounts macroN cn ratios resolutions) 1 q 0 [])
    (fun q i => canonicalCounter (sourceCounts macroN cn ratios resolutions) 0 q 0 [i.val]) δ c 0
    (t/(n+1),quadraticSourceData macroN n D 1 t cn ratios resolutions z.2.1 z.2.2.1)
    z.1 (quadraticNetworkQueries z.1) z.2.2.2).symm

theorem quadraticEvaluate_eq_original_of_germ
    (s : PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D) (t : ℕ)
    (C : TransportAuxiliaryFrame.Store
      (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) 0))
      (auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) 0) D)
    (g : Generators (n+1) D (size (n+1) 1 1 1 t)) (w : QuadraticQuery n D)
    (he : let M := sourcePhysicalMacro macroN 0 n D cn ratios resolutions hAll s initial Km
      let G := sourcePhysicalGeometry macroN 0 n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR
      let data := quadraticSourceData macroN n D 1 t cn ratios resolutions C g
      quadraticCore (physicalRotations s.1) M ν G ρ R =ᶠ[𝓝 (quadraticUpperProjection n D w)]
        prefixQuadraticCore (physicalRotations s.1) M ν G ρ R
          (counter (sourceCounts macroN cn ratios resolutions) 1 (t/(n+1)) 0 [])
          (fun i => canonicalCounter (sourceCounts macroN cn ratios resolutions) 0 (t/(n+1)) 0 [i.val])
          data.1 data.2.1 data.2.2) :
    quadraticEvaluate macroN n D cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν ρ R δ c t
      (w,(C,(g,batch (augment g (quadraticNetworkQueries w)) s.1)))=
      quadraticOriginalReply macroN n D cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν ρ R δ c s w := by
  rw [quadraticEvaluate_template_independent macroN n D cn ratios resolutions hdim hAll hT
    initial weight A Kminus ζ CR Km ν ρ R δ c s t]
  exact prefixQuadraticJointReply_eq_actual_of_germ (physicalRotations s.1)
    (sourcePhysicalMacro macroN 0 n D cn ratios resolutions hAll s initial Km) ν
    (sourcePhysicalGeometry macroN 0 n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR) ρ R
    (fun q => counter (sourceCounts macroN cn ratios resolutions) 1 q 0 [])
    (fun q i => canonicalCounter (sourceCounts macroN cn ratios resolutions) 0 q 0 [i.val])
    (t/(n+1),quadraticSourceData macroN n D 1 t cn ratios resolutions C g) δ c g
    (quadraticNetworkQueries w) s.1 0 w (quadraticNetworkQueries_physical w) he

end Bilevel.TransportHierarchy
