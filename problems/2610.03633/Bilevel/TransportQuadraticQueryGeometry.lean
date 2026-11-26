import Bilevel.PrimitiveQueryGeometry
import Bilevel.TransportQuadraticOracleProperty

/-! Public finite geometry and scalar conservativity of the literal physical
quadratic transport oracle. Neither depends on the selected algorithm. -/
noncomputable section
namespace Bilevel.PrimitiveQuery
open PrimitiveGeometry TransportHierarchy EndpointTransportResponse
set_option autoImplicit false

def quadraticGeometry (n D : ℕ) (hD : 0<D) : Geometry := by
  letI : NeZero D := ⟨hD.ne'⟩
  letI : MeasurableSpace (QuadraticOutput D) := borel _
  letI : BorelSpace (QuadraticOutput D) := ⟨rfl⟩
  letI : MeasurableSpace (Physical n D) := borel _
  letI : BorelSpace (Physical n D) := ⟨rfl⟩
  letI : MeasurableSpace (QuadraticQuery n D) := borel _
  letI : BorelSpace (QuadraticQuery n D) := ⟨rfl⟩
  exact Geometry.of (QuadraticOutput D) (Physical n D)

end Bilevel.PrimitiveQuery

namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  ChiExtensionCalibration EndpointTransportResponse PrimitiveGeometry
set_option autoImplicit false
variable (macroN n D : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) 0,chainSize i+1≤D)
  (hT : capacity (sourceCounts macroN cn ratios resolutions) 1 0≤D)
  (sc : Scale) (weight : ℕ → ℝ) (ζ CR Km : ℝ) (rad R : ℕ → ℝ)

theorem quadraticOriginalReply_conservative (δ c : ℝ)
    (a : PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D) :
    ∃ f g : QuadraticQuery n D → ℝ,
      (∀ q,HasGradientAt f
        (quadraticOriginalReply macroN n D cn ratios resolutions hdim hAll hT sc weight 3 1 ζ CR Km
          (sc.curvature/24) (rad 0) (R 0) δ c a q).1 q) ∧
      (∀ q,HasGradientAt g
        (quadraticOriginalReply macroN n D cn ratios resolutions hdim hAll hT sc weight 3 1 ζ CR Km
          (sc.curvature/24) (rad 0) (R 0) δ c a q).2 q) := by
  let Q := physicalRotations a.1
  let M := sourcePhysicalMacro macroN 0 n D cn ratios resolutions hAll a sc Km
  let G := sourcePhysicalGeometry macroN 0 n D cn ratios resolutions hdim hT a sc weight 3 1 ζ CR
  let f := quadraticFullCore Q M (sc.curvature/24) G (rad 0) (R 0)
  let g : QuadraticQuery n D → ℝ := ChiQuadratic.lower (physicalHessian δ Q) (endpointCoupling c Q)
  have hf : Differentiable ℝ f := (quadraticFullCore_contDiff _ _ _ _ _ _).differentiable (by norm_num)
  have hg : Differentiable ℝ g := (ChiQuadratic.lower_contDiff _ _ 3).differentiable (by norm_num)
  exact ⟨f,g,fun q => (hf q).hasGradientAt,fun q => (hg q).hasGradientAt⟩

end Bilevel.TransportHierarchy
