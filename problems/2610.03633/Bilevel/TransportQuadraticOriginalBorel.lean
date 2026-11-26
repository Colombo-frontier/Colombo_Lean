import Bilevel.TransportQuadraticFullDisclosure
import Bilevel.EndpointTransportFullDisclosure

/-! Joint Borel dependence of the original full SFO pair on the fixed
physical instance and arbitrary full query. Complete arrays are used only
to represent the original family, never as data supplied to its compiler. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiExtensionCalibration
  EndpointTransportResponse TransportRound TransportNetwork PrimitiveGeometry PartialLegendre ChiCarrier
set_option autoImplicit false
set_option maxHeartbeats 1500000

variable (macroN n D : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) 0,chainSize i+1≤D)
  (hT : capacity (sourceCounts macroN cn ratios resolutions) 1 0≤D)
  (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km ν ρ R : ℝ)
  (hl : 0< initial.curvature) (hw : 0< initial.width)
  (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hη1 : ∀ j,resolutions j≤1)
  (hweight : ∀ j,0<weight j) (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km)

include hl hw hr hη hη1 hweight hζ hCR hKm in
theorem quadraticOriginalUpper_full
    (s : PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D) :
    quadraticFullCore (physicalRotations s.1)
      (sourcePhysicalMacro macroN 0 n D cn ratios resolutions hAll s initial Km) ν
      (sourcePhysicalGeometry macroN 0 n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR) ρ R=
    prefixQuadraticUpper (fun _ => LinearIsometryEquiv.refl ℝ (Block D))
      (sourcePhysicalMacro macroN 0 n D cn ratios resolutions hAll
        (templateSample (sourceCounts macroN cn ratios resolutions) 0 n D) initial Km) ν
      (sourcePhysicalGeometry macroN 0 n D cn ratios resolutions hdim hT
        (templateSample (sourceCounts macroN cn ratios resolutions) 0 n D) initial weight A Kminus ζ CR) ρ R
      (fun _ => macroN+1) (fun _ _ => sourceChainIndex cn (ratios 0) (resolutions 0)+1)
      (0,completeQuadraticData macroN n D cn ratios resolutions hAll hT s) := by
  let M := sourcePhysicalMacro macroN 0 n D cn ratios resolutions hAll s initial Km
  let G := sourcePhysicalGeometry macroN 0 n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR
  have geo := sourcePhysical_geometry macroN 0 n D cn ratios resolutions hdim hAll hT s
    initial weight A Kminus ζ CR Km hl hw hr hη hη1 hweight hζ hCR hKm
  have he := quadraticCore_full_prefix (physicalRotations s.1) M ν G ρ R
    (completeQuadraticData macroN n D cn ratios resolutions hAll hT s)
    (fun _ => rfl)
    (completeQuadraticData_source macroN n D cn ratios resolutions hAll hT hdim s initial weight A Kminus ζ CR)
    (completeQuadraticData_target macroN n D cn ratios resolutions hAll hT hdim s initial weight A Kminus ζ CR)
    geo.1 (fun i => (geo.2.2.1 0 [i.val]).1)
    (fun i => (geo.2.2.1 0 [i.val]).2.2.2.1) (fun i => (geo.2.2.1 0 [i.val]).2.2.2.2)
  funext w
  change quadraticCore (physicalRotations s.1) M ν G ρ R (quadraticUpperProjection n D w)=_
  rw [he]
  exact congrFun (prefixQuadraticCore_reframe (physicalRotations s.1)
    (fun _ => LinearIsometryEquiv.refl ℝ (Block D))
    (sourcePhysicalMacro macroN 0 n D cn ratios resolutions hAll
      (templateSample (sourceCounts macroN cn ratios resolutions) 0 n D) initial Km)
    (physicalMacroFrame hAll s) ν
    (sourcePhysicalGeometry macroN 0 n D cn ratios resolutions hdim hT
      (templateSample (sourceCounts macroN cn ratios resolutions) 0 n D) initial weight A Kminus ζ CR)
    (physicalFamily hdim hT s) ρ R (macroN+1)
    (fun _ => sourceChainIndex cn (ratios 0) (resolutions 0)+1)
    (completeQuadraticData macroN n D cn ratios resolutions hAll hT s)) _

section Measurable
variable [MeasurableSpace (Physical n D)] [BorelSpace (Physical n D)]
  [MeasurableSpace (QuadraticOutput D)] [BorelSpace (QuadraticOutput D)]
  [MeasurableSpace (QuadraticQuery n D)] [BorelSpace (QuadraticQuery n D)]

include hl hw hr hη hη1 hweight hζ hCR hKm in
omit [MeasurableSpace (QuadraticOutput D)] [BorelSpace (QuadraticOutput D)] in
theorem quadraticOriginalUpperGradient_measurable :
    Measurable (fun p : PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D × QuadraticQuery n D =>
      gradient (quadraticFullCore (physicalRotations p.1.1)
        (sourcePhysicalMacro macroN 0 n D cn ratios resolutions hAll p.1 initial Km) ν
        (sourcePhysicalGeometry macroN 0 n D cn ratios resolutions hdim hT p.1 initial weight A Kminus ζ CR) ρ R) p.2) := by
  let Z := PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D × QuadraticQuery n D
  have hd := (completeQuadraticData_measurable macroN n D cn ratios resolutions hAll hT).comp
    (measurable_fst : Measurable (fun p : Z => p.1))
  have hm := (prefixQuadraticUpperGradient_measurable
    (fun _ => LinearIsometryEquiv.refl ℝ (Block D))
    (sourcePhysicalMacro macroN 0 n D cn ratios resolutions hAll
      (templateSample (sourceCounts macroN cn ratios resolutions) 0 n D) initial Km) ν
    (sourcePhysicalGeometry macroN 0 n D cn ratios resolutions hdim hT
      (templateSample (sourceCounts macroN cn ratios resolutions) 0 n D) initial weight A Kminus ζ CR) ρ R
    (fun _ => macroN+1) (fun _ _ => sourceChainIndex cn (ratios 0) (resolutions 0)+1)).comp
      (((measurable_const : Measurable (fun _ : Z => (0 : ℕ))).prodMk hd).prodMk measurable_snd)
  convert hm using 1
  funext p
  rw [quadraticOriginalUpper_full macroN n D cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν ρ R
    hl hw hr hη hη1 hweight hζ hCR hKm p.1]
  rfl

theorem quadraticOriginalLowerGradient_measurable (δ c : ℝ) :
    Measurable (fun p : PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D × QuadraticQuery n D =>
      gradient (ChiQuadratic.lower (physicalHessian δ (physicalRotations p.1.1))
        (endpointCoupling c (physicalRotations p.1.1))) p.2) := by
  let Z := PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D × QuadraticQuery n D
  let g : Generators (n+1) D 0 := fun _ _ => 0
  have hq : Measurable (fun p : Z => quadraticNetworkQueries p.2) := quadraticNetworkQueries_measurable.comp measurable_snd
  have hz : Measurable (fun p : Z => p.1.1) := measurable_fst.comp measurable_fst
  have hb := (batch_joint_measurable (n+1) D (0+1)).comp
    (((augment_measurable (n+1) D 0 1).comp
      ((measurable_const : Measurable (fun _ : Z => g)).prodMk hq)).prodMk hz)
  have hx : Measurable (fun p : Z => p.2.fst) :=
    (jointFstLinear (A:=QuadraticOutput D) (B:=Physical n D)).continuous.measurable.comp measurable_snd
  have hm := (batchLowerGradient_measurable (n:=n) (D:=D) (m:=0) δ c (0 : Fin 1)).comp
    (hx.prodMk (hq.prodMk hb))
  convert hm using 1
  funext p
  have he := batchLowerGradient_actual δ c g (quadraticNetworkQueries p.2) p.1.1 (0 : Fin 1) p.2.fst
  rw [quadraticNetworkQueries_physical] at he
  exact he.symm

include hl hw hr hη hη1 hweight hζ hCR hKm in
theorem quadraticOriginalReply_measurable (δ c : ℝ) :
    Measurable (fun p : PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D × QuadraticQuery n D =>
      quadraticOriginalReply macroN n D cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν ρ R δ c p.1 p.2) :=
  (quadraticOriginalUpperGradient_measurable macroN n D cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν ρ R
    hl hw hr hη hη1 hweight hζ hCR hKm).prodMk
    (quadraticOriginalLowerGradient_measurable macroN n D cn ratios resolutions δ c)

end Measurable
end Bilevel.TransportHierarchy
