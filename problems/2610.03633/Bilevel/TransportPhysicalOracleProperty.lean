import Bilevel.TransportPhysicalOriginal
import Bilevel.ChiExactDifferentiableOracle
import Bilevel.EndpointTransportOracleScalars

/-! The literal positive-depth physical reply is the complete conservative
pointmass SFO pair of the same retained Primitive.  No information bound or
algorithmic history is assumed in this identification. -/
noncomputable section
open MeasureTheory
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

def HasPhysicalFullOracle (μ L ρg : ℝ)
    (a : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D)
    (Pr : Model.Primitive (X:=HybridOuter (Block D) (Blocks J (Block D)) D)
      (Y:=HybridVariables (Blocks J (Block D)) (Normals s) n D) μ L L L ρg) : Prop :=
  ∀ [MeasurableSpace (PhysicalQuery J n D s)] [BorelSpace (PhysicalQuery J n D s)]
    [SecondCountableTopology (PhysicalQuery J n D s)],∀ σf σg : ℝ,
    ∃ Of : FreshOracle.Oracle (Query:=PhysicalQuery J n D s) (E:=PhysicalQuery J n D s) (Measure.dirac ()) σf,
    ∃ Og : FreshOracle.Oracle (Query:=PhysicalQuery J n D s) (E:=PhysicalQuery J n D s) (Measure.dirac ()) σg,
      (∀ q,Of.truth q=pack (Pr.fx q.fst q.snd) (Pr.fy q.fst q.snd)) ∧
      (∀ q,Og.truth q=pack (Pr.gx q.fst q.snd) (Pr.gy q.fst q.snd)) ∧
      ∀ q coin,(Of.sample q coin,Og.sample q coin)=
        physicalOriginalReply macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν
          fine index radialIndex fineIndex ρ R dn (dn • normalOnes s) m δ c₀ cend
          ⟨1/12,by norm_num⟩ (by change (1:ℝ)/12<1;norm_num) hF a q

theorem hasPhysicalFullOracle (μ L ρg : ℝ)
    (a : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D)
    (Pr : Model.Primitive (X:=HybridOuter (Block D) (Blocks J (Block D)) D)
      (Y:=HybridVariables (Blocks J (Block D)) (Normals s) n D) μ L L L ρg)
    (hExt : ContDiff ℝ 3 (physicalOriginalPotential macroN J n D s cn ratios resolutions hdim hAll hT
      initial weight A Kminus ζ CR Km fine index radialIndex fineIndex ρ R dn a))
    (hf : ∀ x y,Pr.f x y=physicalOriginalUpper macroN J n D s cn ratios resolutions hdim hAll hT
      initial weight A Kminus ζ CR Km ν ρ R (dn • normalOnes s) a (pack x y))
    (hg : ∀ x y,Pr.g x y=physicalOriginalLower macroN J n D s cn ratios resolutions hdim hAll hT
      initial weight A Kminus ζ CR Km fine index radialIndex fineIndex ρ R dn m δ c₀ cend
      ⟨1/12,by norm_num⟩ (by change (1:ℝ)/12<1;norm_num) hF a (pack x y)) :
    HasPhysicalFullOracle macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν
      fine index radialIndex fineIndex ρ R dn m δ c₀ cend hF μ L ρg a Pr := by
  intro instM instB instS σf σg
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
  exact ChiPrimitive.full_joint_oracles_exact_differentiable Pr f g hfd hgd hf hg σf σg

end Bilevel.TransportHierarchy
