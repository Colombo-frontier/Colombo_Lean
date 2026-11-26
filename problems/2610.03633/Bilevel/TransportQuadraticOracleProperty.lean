import Bilevel.TransportQuadraticPublicWitness
import Bilevel.TransportQuadraticOriginal
import Bilevel.ChiExactJointOracle

/-! The compiler's literal deterministic reply is an original complete
SFO pair for the same retained Primitive, with conservative exact samples. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  ChiExtensionCalibration EndpointTransportResponse PrimitiveGeometry
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable (macroN n D : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) 0,chainSize i+1≤D)
  (hT : capacity (sourceCounts macroN cn ratios resolutions) 1 0≤D)
  (sc : Scale) (weight : ℕ → ℝ) (ζ CR Km : ℝ) (rad R : ℕ → ℝ)

def HasQuadraticFullOracle (μ L ρg δ c : ℝ)
    (a : PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D)
    (P : Model.Primitive (X:=QuadraticOutput D) (Y:=Physical n D) μ L L L ρg) : Prop :=
  ∀ [MeasurableSpace (QuadraticQuery n D)] [BorelSpace (QuadraticQuery n D)] [SecondCountableTopology (QuadraticQuery n D)],
    ∀ σf σg : ℝ,
    ∃ Of : FreshOracle.Oracle (Query:=QuadraticQuery n D) (E:=QuadraticQuery n D) (Measure.dirac ()) σf,
    ∃ Og : FreshOracle.Oracle (Query:=QuadraticQuery n D) (E:=QuadraticQuery n D) (Measure.dirac ()) σg,
      (∀ q,Of.truth q=pack (P.fx q.fst q.snd) (P.fy q.fst q.snd)) ∧
      (∀ q,Og.truth q=pack (P.gx q.fst q.snd) (P.gy q.fst q.snd)) ∧
      ∀ q coin,(Of.sample q coin,Og.sample q coin)=
        quadraticOriginalReply macroN n D cn ratios resolutions hdim hAll hT sc weight 3 1 ζ CR Km
          (sc.curvature/24) (rad 0) (R 0) δ c a q

theorem hasQuadraticFullOracle (μ L ρg δ c : ℝ)
    (a : PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D)
    (P : Model.Primitive (X:=QuadraticOutput D) (Y:=Physical n D) μ L L L ρg)
    (hf : ∀ x y,P.f x y=quadraticCore (physicalRotations a.1)
      (sourcePhysicalMacro macroN 0 n D cn ratios resolutions hAll a sc Km) (sc.curvature/24)
      (sourcePhysicalGeometry macroN 0 n D cn ratios resolutions hdim hT a sc weight 3 1 ζ CR) (rad 0) (R 0) (pack x.fst y))
    (hg : ∀ x y,P.g x y=lower δ c (physicalRotations a.1) x.snd y) :
    HasQuadraticFullOracle macroN n D cn ratios resolutions hdim hAll hT sc weight ζ CR Km rad R μ L ρg δ c a P := by
  intro instM instB instS σf σg
  let Q := physicalRotations a.1
  let M := sourcePhysicalMacro macroN 0 n D cn ratios resolutions hAll a sc Km
  let G := sourcePhysicalGeometry macroN 0 n D cn ratios resolutions hdim hT a sc weight 3 1 ζ CR
  let f : QuadraticQuery n D → ℝ := quadraticFullCore Q M (sc.curvature/24) G (rad 0) (R 0)
  let g : QuadraticQuery n D → ℝ := ChiQuadratic.lower (physicalHessian δ Q) (endpointCoupling c Q)
  have hPf : ∀ x y,P.f x y=f (pack x y) := hf
  have hPg : ∀ x y,P.g x y=g (pack x y) := fun x y => (hg x y).trans (lower_eq_quadratic δ c Q x y).symm
  exact ChiPrimitive.full_joint_oracles_exact P f g
    (quadraticFullCore_contDiff Q M (sc.curvature/24) G (rad 0) (R 0))
    (ChiQuadratic.lower_contDiff _ _ 3) hPf hPg σf σg

end Bilevel.TransportHierarchy
