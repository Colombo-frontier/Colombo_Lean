import Bilevel.TransportHierarchyAncestorProjection

/-! Opaque source-wide projected margins.  Numerical budgets are paid by
the same public cap, independently of the ambient dimension and sample. -/
noncomputable section
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiExtensionCalibration
  ChiHierarchyHaar ChiHierarchyExecution EndpointTransportResponse PrimitiveGeometry TransportRound TransportNetwork
set_option autoImplicit false
set_option maxHeartbeats 600000

variable (macroN J n D : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤D)
  (hT : capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0≤D)
  (hA : auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) J+1≤D)
  (s : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D)
  (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km : ℝ)

local notation "cts" => sourceCounts macroN cn ratios resolutions
local notation "G" => sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR

include hAll in
theorem sourcePhysical_ancestor_margins
    (hl : 0< initial.curvature) (hw : 0< initial.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hη1 : ∀ j,resolutions j≤1)
    (hweight : ∀ j,0<weight j) (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km)
    (q : ℕ) (W : Fin J → Submodule ℝ (EuclideanGaussian.Space D)) (τ : ℝ) (hτ : 0<τ)
    (hE : ∀ j I,∀ hj : j<J,GenieProtocol.BoundedEnergy (W ⟨j,hj⟩)
      (prefixSet (canonicalCounter cts J q j I))
      (TransportNetworkAuxiliary.auxiliaryFrame (auxiliaryCapacity cts J+1) hA
        (enumerate cts J (Sum.inr (canonicalNode cts J ⟨j,Nat.lt_succ_of_lt hj⟩ I))) s)
      (sourcePublicCap macroN J initial ratios resolutions weight CR ζ Km τ)) :
    ∀ j I,∀ hj : j<J,∀ k : Fin ((G j I).n+1),canonicalCounter cts J q j I≤k.val →
      (G j I).radius*‖(W ⟨j,hj⟩).orthogonalProjection ((G j I).frame (basis k))‖≤(G j I).width/8 := by
  have geo := sourcePhysical_geometry macroN J n D cn ratios resolutions hdim hAll hT s
    initial weight A Kminus ζ CR Km hl hw hr hη hη1 hweight hζ hCR hKm
  have cap := sourcePublicCap_budgets macroN J initial ratios resolutions weight CR ζ Km τ
    hl hw hr hη hweight hCR hζ hKm hτ
  intro j I hj k hk
  exact sourcePhysical_ancestor_projection macroN J n D cn ratios resolutions hdim hAll hT hA s
    initial weight A Kminus ζ CR q j hj I (W ⟨j,hj⟩) _ cap.1.le (hE j I hj)
    (geo.2.2.1 j I).2.1.le (cap.2.2 (Sum.inr (Sum.inl ⟨j,Nat.lt_succ_of_lt hj⟩))) k hk

end Bilevel.TransportHierarchy
