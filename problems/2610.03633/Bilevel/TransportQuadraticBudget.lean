import Bilevel.TransportUniformDimension
import Bilevel.TransportPublicCapBounds
import Bilevel.TransportHierarchyAuxiliarySchedule
import Bilevel.EndpointTransportResponse

/-! Dimension calibration for the actual quadratic compiler. The same
public dimension covers every capped execution up to H. -/
noncomputable section
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiRecursive ChiExtensionCalibration TransportAugmented
set_option autoImplicit false

def quadraticBudget (macroN n D : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
    (initial : Scale) (weight : ℕ → ℝ) (CR ζ Km τ β : ℝ) (N : ℕ) : Prop :=
  let counts := sourceCounts macroN cn ratios resolutions
  let k := Fintype.card (FrameIndex counts 0)
  let T := auxiliaryCapacity counts 0
  let cap := sourcePublicCap macroN 0 initial ratios resolutions weight CR ζ Km τ
  ObserverBudget (n+1) 1 (capacity counts 1 0) k T (k*(T+1)+1) D N
    (Real.sqrt cap/EndpointTransportMatrix.gamma n) cap β

theorem exists_quadratic_dimension (D₀ macroN n H : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
    (initial : Scale) (weight : ℕ → ℝ) (CR ζ Km τ β : ℝ)
    (hc : 0<sourcePublicCap macroN 0 initial ratios resolutions weight CR ζ Km τ)
    (hβ : 0<β) (hβ1 : β≤1) :
    ∃ D : ℕ,D₀≤D ∧ capacity (sourceCounts macroN cn ratios resolutions) 1 0≤D ∧
      auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) 0+1≤D ∧
      ∀ N : ℕ,N≤H → quadraticBudget macroN n D cn ratios resolutions initial weight CR ζ Km τ β N := by
  let counts := sourceCounts macroN cn ratios resolutions
  exact exists_uniform_joint_dimension D₀ (n+1) 1 (capacity counts 1 0)
    (Fintype.card (FrameIndex counts 0)) (auxiliaryCapacity counts 0) H
    (Fintype.card (FrameIndex counts 0)*(auxiliaryCapacity counts 0+1)+1)
    (Real.sqrt (sourcePublicCap macroN 0 initial ratios resolutions weight CR ζ Km τ)/EndpointTransportMatrix.gamma n)
    (sourcePublicCap macroN 0 initial ratios resolutions weight CR ζ Km τ) β
    (frame_count_positive counts 0) hc hβ hβ1

end Bilevel.TransportHierarchy
