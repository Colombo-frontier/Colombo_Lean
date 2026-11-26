import Bilevel.TransportHierarchySourceGeometry
import Bilevel.TransportHierarchyAuxiliaryReadout
import Bilevel.TransportHierarchyPreSpace
import Bilevel.ChiCanonicalProjection

/-! Actual auxiliary energy and actual network projection events imply
the weighted projection bounds of the physical source. The public network
norm cap is sqrt(cap)/gamma; no dimension-dependent scale is introduced. -/
noncomputable section
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiExtensionCalibration
  ChiHierarchyHaar ChiHierarchyExecution TransportRound TransportNetwork EndpointTransportResponse
set_option maxHeartbeats 900000

variable (macroN J n D : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤D)
  (hT : capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0≤D)
  (hA : auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) J+1≤D)
  (s : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D)

theorem sourcePhysical_macro_projection (initial : Scale) (Km : ℝ)
    (WM : Submodule ℝ (EuclideanGaussian.Space D)) (q : ℕ) (cap : ℝ) (hcap : 0≤cap)
    (hE : GenieProtocol.BoundedEnergy WM
      (prefixSet (counter (sourceCounts macroN cn ratios resolutions) (J+1) q 0 []))
      (TransportNetworkAuxiliary.auxiliaryFrame (auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) J+1)
        hA (enumerate (sourceCounts macroN cn ratios resolutions) J (Sum.inl ())) s) cap)
    (hR : 0≤(sourcePhysicalMacro macroN J n D cn ratios resolutions hAll s initial Km).radius)
    (hbudget : (sourcePhysicalMacro macroN J n D cn ratios resolutions hAll s initial Km).radius*Real.sqrt cap≤
      (sourcePhysicalMacro macroN J n D cn ratios resolutions hAll s initial Km).width/8)
    (k : Fin (macroN+1)) (hk : counter (sourceCounts macroN cn ratios resolutions) (J+1) q 0 []≤k.val) :
    (sourcePhysicalMacro macroN J n D cn ratios resolutions hAll s initial Km).radius*
      ‖WM.orthogonalProjection ((sourcePhysicalMacro macroN J n D cn ratios resolutions hAll s initial Km).frame (basis k))‖≤
        (sourcePhysicalMacro macroN J n D cn ratios resolutions hAll s initial Km).width/8 := by
  have hp := frame_projection_norm_bound WM _ _ cap hcap hE
    (auxiliaryColumnIndex (sourceCounts macroN cn ratios resolutions) J (Sum.inl ()) k) hk
  rw [auxiliary_column_nested hAll hA s (Sum.inl ()) k] at hp
  exact (mul_le_mul_of_nonneg_left hp hR).trans hbudget

theorem source_network_cap_positive (cap : ℝ) (hcap : 0<cap) :
    0<Real.sqrt cap/EndpointTransportMatrix.gamma n :=
  div_pos (Real.sqrt_pos.mpr hcap) (gamma_positive n)

theorem source_network_radius_budget (radius width cap : ℝ)
    (hbudget : radius*Real.sqrt cap≤width/8) :
    (EndpointTransportMatrix.gamma n*radius)*(Real.sqrt cap/EndpointTransportMatrix.gamma n)≤width/8 := by
  have hγ := ne_of_gt (gamma_positive n)
  calc
    _=radius*Real.sqrt cap := by field_simp;ring
    _≤width/8 := hbudget

theorem sourcePhysical_terminal_projection {H : Type*} {p : ℕ}
    (choose : ∀ t,H × Generators (n+1) D (size (n+1) p 1 1 t) → Queries (n+1) D p)
    (respond : ∀ t,StepData H (n+1) D (size (n+1) p 1 1 t) p
      (capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0) → H)
    (memory : H) (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR : ℝ)
    (N t : ℕ) (ht : t<N) (cap : ℝ)
    (hnet : ProjectionGood hT choose respond N (Real.sqrt cap/EndpointTransportMatrix.gamma n) memory s.1)
    (I : List ℕ) (k : Fin (sourceChainIndex cn (ratios J) (resolutions J)+1))
    (hk : canonicalCounter (sourceCounts macroN cn ratios resolutions) J (t/(n+1)) J I≤k.val)
    (hR : 0≤(sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR J I).radius)
    (hbudget : (sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR J I).radius*
      Real.sqrt cap≤(sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR J I).width/8) :
    (EndpointTransportMatrix.gamma n*
      (sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR J I).radius)*
      ‖(terminalPreSpace (sourceCounts macroN cn ratios resolutions) J hT choose respond memory s.1 t (Fin.last (n+1))).orthogonalProjection
        (physicalRotations s.1 (Fin.last (n+1))
          ((sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR J I).frame (basis k)))‖≤
      (sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR J I).width/8 := by
  rw [sourcePhysicalGeometry_frame,physicalFamily_terminal]
  exact terminalTarget_width_margin (sourceCounts macroN cn ratios resolutions) J hT choose respond memory s.1
    N (Real.sqrt cap/EndpointTransportMatrix.gamma n) hnet t ht I k hk _ _ hR
    (source_network_radius_budget n _ _ cap hbudget)

end Bilevel.TransportHierarchy
