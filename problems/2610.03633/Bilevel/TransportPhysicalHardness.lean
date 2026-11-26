import Bilevel.TransportPhysicalQueryFamily

/-! Actual physical expected-rate families give conservative hardness in the
common geometry-indexed original-query model. -/
noncomputable section
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  ChiExtensionCalibration EndpointTransportResponse PrimitiveGeometry PrimitiveQuery ChiExtension
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

theorem physical_conservative_hardness (μ L ρg Δ R₀ σf σg K ε rate : ℝ) (hR₀ : 0≤R₀)
    (hfamily : ∀ a : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D,
      ∃ Pr : Model.Primitive (X:=PhysicalOutput J D)
        (Y:=HybridVariables (Blocks J (Block D)) (Normals s) n D) μ L L L ρg,
      ∃ r : Pr.Response,r.y 0=0 ∧ Nonempty (Pr.GapCertificate r 0 Δ) ∧
      (∀ x,Pr.hyperobjective r x=
        physicalOriginalMean macroN J n D cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν ρ R K a x) ∧
      ContDiff ℝ 3 (physicalOriginalPotential macroN J n D s cn ratios resolutions hdim hAll hT
        initial weight A Kminus ζ CR Km fine index radialIndex fineIndex ρ R dn a) ∧
      HasPhysicalFullOracle macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν
        fine index radialIndex fineIndex ρ R dn m δ c₀ cend hF μ L ρg a Pr)
    (hRate : PhysicalRateProperty macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν
      fine index radialIndex fineIndex ρ R dn (dn • normalOnes s) m δ c₀ cend hF K ε rate) :
    Hardness (conservativeClass (μ:=μ) (L:=L) (ρ:=ρg) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg)) ε rate := by
  classical
  choose Pr r hz hgap hm hExt hFull using hfamily
  obtain ⟨hD,F,hF',hcons,hmean⟩ := physical_query_family macroN J n D s cn ratios resolutions hdim hAll hT
    initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn m δ c₀ cend hF
    μ L ρg Δ R₀ σf σg K ε rate hR₀ Pr r hgap hz hm hExt hFull hRate
  exact F.hardness _ ε rate hcons hF'

end Bilevel.TransportHierarchy
