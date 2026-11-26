import Bilevel.TransportHierarchySourceProjection
import Bilevel.TransportPublicCapBounds

/-! Actual terminal source/target information at the prebatch space.
Source columns use the next reachable counter; target columns use the old
counter.  The source and target remain restrictions of one network frame. -/
noncomputable section
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiExtensionCalibration
  ChiHierarchyHaar EndpointTransportResponse PrimitiveGeometry TransportRound TransportNetwork
set_option autoImplicit false
set_option maxHeartbeats 600000

variable {H : Type*} (macroN J n D p : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤D)
  (hT : capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0≤D)
  (s : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D)
  (choose : ∀ t,H × Generators (n+1) D (size (n+1) p 1 1 t) → Queries (n+1) D p)
  (respond : ∀ t,StepData H (n+1) D (size (n+1) p 1 1 t) p
    (capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0) → H)
  (memory : H) (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km : ℝ)

local notation "cts" => sourceCounts macroN cn ratios resolutions
local notation "G" => sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR
local notation "Q" => physicalRotations (Prod.fst s)
local notation "Z" => terminalPreSpace cts J hT choose respond memory (Prod.fst s)

include hAll in
theorem sourcePhysical_terminal_facts
    (hl : 0< initial.curvature) (hw : 0< initial.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hη1 : ∀ j,resolutions j≤1)
    (hweight : ∀ j,0<weight j) (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km)
    (τ : ℝ) (hτ : 0<τ) (N t : ℕ) (ht : t<N)
    (hnet : ProjectionGood hT choose respond N
      (Real.sqrt (sourcePublicCap macroN J initial ratios resolutions weight CR ζ Km τ)/EndpointTransportMatrix.gamma n)
      memory s.1) :
    (∀ I,∀ k : Fin ((G J I).n+1),k.val<canonicalCounter cts J (t/(n+1)+1) J I →
      Q 0 ((G J I).frame (basis k))∈Z t 0) ∧
    (∀ I,∀ k : Fin ((G J I).n+1),k.val<canonicalCounter cts J (t/(n+1)) J I →
      Q (Fin.last (n+1)) ((G J I).frame (basis k))∈Z t (Fin.last (n+1))) ∧
    (∀ I,∀ k : Fin ((G J I).n+1),canonicalCounter cts J (t/(n+1)) J I≤k.val →
      (EndpointTransportMatrix.gamma n*(G J I).radius)*‖(Z t (Fin.last (n+1))).orthogonalProjection
        (Q (Fin.last (n+1)) ((G J I).frame (basis k)))‖≤(G J I).width/8) := by
  have geo := sourcePhysical_geometry macroN J n D cn ratios resolutions hdim hAll hT s
    initial weight A Kminus ζ CR Km hl hw hr hη hη1 hweight hζ hCR hKm
  have cap := sourcePublicCap_budgets macroN J initial ratios resolutions weight CR ζ Km τ
    hl hw hr hη hweight hCR hζ hKm hτ
  refine ⟨?_,?_,?_⟩
  · intro I k hk
    simpa only [sourcePhysicalGeometry_frame,physicalFamily_terminal] using
      terminalSource_mem_preSpace cts J hT choose respond memory s.1 t I k hk
  · intro I k hk
    simpa only [sourcePhysicalGeometry_frame,physicalFamily_terminal] using
      terminalTarget_mem_preSpace cts J hT choose respond memory s.1 t I k hk
  · intro I k hk
    exact sourcePhysical_terminal_projection macroN J n D cn ratios resolutions hdim hT s choose respond
      memory initial weight A Kminus ζ CR N t ht _ hnet I k hk (geo.2.2.1 J I).2.1.le
      (cap.2.2 (Sum.inr (Sum.inl ⟨J,Nat.lt_succ_self J⟩)))

end Bilevel.TransportHierarchy
