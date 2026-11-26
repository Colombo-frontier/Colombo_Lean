import Bilevel.TransportPhysicalOracleProperty

/-! The exact public source formulas discharge the full-oracle scalar
identities, with the public normal vector and physical hybrid coefficients. -/
noncomputable section
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  ChiExtensionCalibration EndpointTransportResponse PrimitiveGeometry PartialLegendre ChiExtension
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem hasPhysicalSourceFullOracle (macroN J D s : ℕ) (L κ : ℝ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
    (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
    (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤D)
    (hT : capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0≤D)
    (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km ν : ℝ) (fine : ChiFine.Parameters)
    (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (ρ R : ℕ → ℝ) (dn : ℝ)
    (hF : ∀ a : PhysicalSample (sourceCounts macroN cn ratios resolutions) J (EndpointTransportNormalization.interiors κ) D,
      LipschitzWith (⟨1/12,by norm_num⟩ : NNReal)
        (gradient (physicalOriginalPotential macroN J (EndpointTransportNormalization.interiors κ) D s cn ratios resolutions
          hdim hAll hT initial weight A Kminus ζ CR Km fine index radialIndex fineIndex ρ R dn a)))
    (ρg : ℝ) (a : PhysicalSample (sourceCounts macroN cn ratios resolutions) J (EndpointTransportNormalization.interiors κ) D)
    (Pr : Model.Primitive (X:=HybridOuter (Block D) (Blocks J (Block D)) D)
      (Y:=HybridVariables (Blocks J (Block D)) (Normals s) (EndpointTransportNormalization.interiors κ) D) (L/κ) L L L ρg)
    (hExt : ContDiff ℝ 3 (physicalOriginalPotential macroN J (EndpointTransportNormalization.interiors κ) D s cn ratios resolutions
      hdim hAll hT initial weight A Kminus ζ CR Km fine index radialIndex fineIndex ρ R dn a))
    (hExt2 : ∀ z,‖iteratedFDeriv ℝ 2 (physicalOriginalPotential macroN J (EndpointTransportNormalization.interiors κ) D s
      cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km fine index radialIndex fineIndex ρ R dn a) z‖≤(1:ℝ)/12)
    (hf : ∀ x y,Pr.f x y=physicalUpperBase J (physicalRotations a.1)
      (sourcePhysicalMacro macroN J (EndpointTransportNormalization.interiors κ) D cn ratios resolutions hAll a initial Km) ν
      (sourcePhysicalGeometry macroN J (EndpointTransportNormalization.interiors κ) D cn ratios resolutions hdim hT a initial weight A Kminus ζ CR)
      J (ρ 0) (R 0) (pack x.fst.fst y.fst)+dn*normalReadout s y.snd)
    (hg : ∀ x y,Pr.g x y=sourceHybridLower L κ (physicalRotations a.1)
      (physicalOriginalPotential macroN J (EndpointTransportNormalization.interiors κ) D s cn ratios resolutions
        hdim hAll hT initial weight A Kminus ζ CR Km fine index radialIndex fineIndex ρ R dn a) hExt
      ⟨1/12,by norm_num⟩ hExt2 (by change (1:ℝ)/12<1;norm_num) (pack x y)) :
    HasPhysicalFullOracle macroN J (EndpointTransportNormalization.interiors κ) D s cn ratios resolutions hdim hAll hT
      initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn
      (3*(L/κ)/2) (L/16) (EndpointTransportNormalization.coupling L κ) (L/4) hF (L/κ) L ρg a Pr := by
  apply hasPhysicalFullOracle macroN J (EndpointTransportNormalization.interiors κ) D s cn ratios resolutions hdim hAll hT
    initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn
    (3*(L/κ)/2) (L/16) (EndpointTransportNormalization.coupling L κ) (L/4) hF (L/κ) L ρg a Pr hExt
  · intro x y
    exact (hf x y).trans (physicalUpper_public_normal _ dn (pack x y)).symm
  · intro x y
    exact (hg x y).trans (congrFun (sourceHybridLower_certificate L κ (physicalRotations a.1) _ hExt
      ⟨1/12,by norm_num⟩ ⟨1/12,by norm_num⟩ hExt2 (by change (1:ℝ)/12<1;norm_num)
      (hF a) (by change (1:ℝ)/12<1;norm_num)) (pack x y))

end Bilevel.TransportHierarchy
