import Bilevel.PrimitiveQueryGeometry
import Bilevel.TransportPhysicalOracleProperty

/-! Public finite geometry and global conservativity of the actual physical
full reply, independently of algorithms and information events. -/
noncomputable section
namespace Bilevel.PrimitiveQuery
open PrimitiveGeometry TransportHierarchy EndpointTransportResponse ChiExtension ChiCarrier
set_option autoImplicit false

def physicalGeometry (J n D s : ℕ) (hD : 0<D) : Geometry := by
  letI : NeZero D := ⟨hD.ne'⟩
  let Y := HybridVariables (Blocks J (Block D)) (Normals s) n D
  letI : Nontrivial Y := Function.Surjective.nontrivial
    (f:=fun y : Y => y.fst.snd) (fun v => ⟨pack (pack 0 v) 0,rfl⟩)
  letI : MeasurableSpace (PhysicalOutput J D) := borel _
  letI : BorelSpace (PhysicalOutput J D) := ⟨rfl⟩
  letI : MeasurableSpace Y := borel _
  letI : BorelSpace Y := ⟨rfl⟩
  letI : MeasurableSpace (PhysicalQuery J n D s) := borel _
  letI : BorelSpace (PhysicalQuery J n D s) := ⟨rfl⟩
  exact Geometry.of (PhysicalOutput J D) Y

end Bilevel.PrimitiveQuery

namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  ChiExtensionCalibration EndpointTransportResponse PrimitiveGeometry PartialLegendre ChiExtension
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable (macroN J n D s : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤D)
  (hT : capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0≤D)
  (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km ν : ℝ) (fine : ChiFine.Parameters)
  (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (ρ R : ℕ → ℝ) (dn m δ c₀ cend : ℝ)
  (hF : ∀ a : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D,
    LipschitzWith (⟨1/12,by norm_num⟩ : NNReal)
      (gradient (physicalOriginalPotential macroN J n D s cn ratios resolutions hdim hAll hT
        initial weight A Kminus ζ CR Km fine index radialIndex fineIndex ρ R dn a)))

theorem physicalOriginalReply_conservative
    (a : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D)
    (hExt : ContDiff ℝ 3 (physicalOriginalPotential macroN J n D s cn ratios resolutions hdim hAll hT
      initial weight A Kminus ζ CR Km fine index radialIndex fineIndex ρ R dn a)) :
    ∃ f g : PhysicalQuery J n D s → ℝ,
      (∀ q,HasGradientAt f (physicalOriginalReply macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν
        fine index radialIndex fineIndex ρ R dn (dn • normalOnes s) m δ c₀ cend
        ⟨1/12,by norm_num⟩ (by change (1:ℝ)/12<1;norm_num) hF a q).1 q) ∧
      (∀ q,HasGradientAt g (physicalOriginalReply macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν
        fine index radialIndex fineIndex ρ R dn (dn • normalOnes s) m δ c₀ cend
        ⟨1/12,by norm_num⟩ (by change (1:ℝ)/12<1;norm_num) hF a q).2 q) := by
  let Q := physicalRotations a.1
  let M := sourcePhysicalMacro macroN J n D cn ratios resolutions hAll a initial Km
  let G := sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT a initial weight A Kminus ζ CR
  let F := physicalOriginalPotential macroN J n D s cn ratios resolutions hdim hAll hT
    initial weight A Kminus ζ CR Km fine index radialIndex fineIndex ρ R dn a
  let f := physicalOriginalUpper macroN J n D s cn ratios resolutions hdim hAll hT
    initial weight A Kminus ζ CR Km ν ρ R (dn • normalOnes s) a
  let g := physicalOriginalLower macroN J n D s cn ratios resolutions hdim hAll hT
    initial weight A Kminus ζ CR Km fine index radialIndex fineIndex ρ R dn m δ c₀ cend
    ⟨1/12,by norm_num⟩ (by change (1:ℝ)/12<1;norm_num) hF a
  have hfd : Differentiable ℝ f :=
    (physicalUpper_contDiff (physicalUpperBase J Q M ν G J (ρ 0) (R 0))
      (physicalUpperBase_contDiff J Q M ν G J (ρ 0) (R 0)) (dn • normalOnes s)).differentiable (by norm_num)
  have hgrad : ∀ z,HasGradientAt F (gradient F z) z :=
    fun z => (hExt.differentiable (by norm_num) z).hasGradientAt
  have hsym := ChiHybrid.correction_symmetric (hybridHessian (U:=Blocks J (Block D)) (V:=Normals s) m δ Q) m
    (hybridHessian_symmetric m δ Q)
  have hgd : Differentiable ℝ g := fun z =>
    (hybridLower_hasGradientAt (hF a) (by change (1:ℝ)/12<1;norm_num) F hgrad m
      (ChiHybrid.correction (hybridHessian m δ Q) m) (hybridCoupling c₀ cend Q) hsym z).differentiableAt
  exact ⟨f,g,fun q => (hfd q).hasGradientAt,fun q => (hgd q).hasGradientAt⟩

end Bilevel.TransportHierarchy
