import Bilevel.TransportPhysicalQueryGeometry
import Bilevel.TransportPhysicalExpectedProperty
import Bilevel.PrimitiveQueryFamilyRealization

/-! The same physical Primitive, response, exact full reply, loss and Unit
stream form an admissible family in the common original-query model. -/
noncomputable section
open MeasureTheory
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

theorem physical_query_family (μ L ρg Δ R₀ σf σg K ε rate : ℝ) (hR₀ : 0≤R₀)
    (Pr : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D →
      Model.Primitive (X:=PhysicalOutput J D)
        (Y:=HybridVariables (Blocks J (Block D)) (Normals s) n D) μ L L L ρg)
    (r : ∀ a,(Pr a).Response)
    (hgap : ∀ a,Nonempty ((Pr a).GapCertificate (r a) 0 Δ))
    (hzero : ∀ a,(r a).y 0=0)
    (hmean : ∀ a x,(Pr a).hyperobjective (r a) x=
      physicalOriginalMean macroN J n D cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν ρ R K a x)
    (hExt : ∀ a,ContDiff ℝ 3 (physicalOriginalPotential macroN J n D s cn ratios resolutions hdim hAll hT
      initial weight A Kminus ζ CR Km fine index radialIndex fineIndex ρ R dn a))
    (hFull : ∀ a,HasPhysicalFullOracle macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν
      fine index radialIndex fineIndex ρ R dn m δ c₀ cend hF μ L ρg a (Pr a))
    (hRate : PhysicalRateProperty macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν
      fine index radialIndex fineIndex ρ R dn (dn • normalOnes s) m δ c₀ cend hF K ε rate) :
    ∃ hD : 0<D,
    ∃ F : PrimitiveQuery.Family (physicalGeometry J n D s hD)
      (PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D) Unit (Measure.dirac ()) μ L ρg Δ R₀ σf σg,
      F.RateProperty ε rate ∧ (∀ a,(F.instance a).IsConservative) ∧
      ∀ a x,(F.primitive a).hyperobjective (F.response a) x=(Pr a).hyperobjective (r a) x := by
  classical
  have hD : 0<D := lt_of_lt_of_le (Nat.succ_pos _) (hdim 0)
  let G := physicalGeometry J n D s hD
  letI : MeasurableSpace (PhysicalOutput J D) := G.measurableX
  letI : BorelSpace (PhysicalOutput J D) := G.borelX
  letI : MeasurableSpace (HybridVariables (Blocks J (Block D)) (Normals s) n D) := G.measurableY
  letI : BorelSpace (HybridVariables (Blocks J (Block D)) (Normals s) n D) := G.borelY
  letI : MeasurableSpace (Physical n D) := borel _
  letI : BorelSpace (Physical n D) := ⟨rfl⟩
  letI : MeasurableSpace (PhysicalQuery J n D s) := G.measurableQuery
  letI : BorelSpace (PhysicalQuery J n D s) := G.borelQuery
  letI : SecondCountableTopology (PhysicalQuery J n D s) := G.countableQuery
  let reply := fun a q (_ : Unit) => physicalOriginalReply macroN J n D s cn ratios resolutions hdim hAll hT
    initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn (dn • normalOnes s) m δ c₀ cend
    ⟨1/12,by norm_num⟩ (by change (1:ℝ)/12<1;norm_num) hF a q
  have horacles (a : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D) :
      ∃ Of : FreshOracle.Oracle (Query:=G.Query) (E:=G.Query) (Measure.dirac ()) σf,
      ∃ Og : FreshOracle.Oracle (Query:=G.Query) (E:=G.Query) (Measure.dirac ()) σg,
        (∀ q,Of.truth q=pack ((Pr a).fx q.fst q.snd) ((Pr a).fy q.fst q.snd)) ∧
        (∀ q,Og.truth q=pack ((Pr a).gx q.fst q.snd) ((Pr a).gy q.fst q.snd)) ∧
        ∀ q coin,(Of.sample q coin,Og.sample q coin)=reply a q coin := hFull a σf σg
  choose Of Og hft hgt hs using horacles
  let F : PrimitiveQuery.Family G
      (PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D) Unit (Measure.dirac ()) μ L ρg Δ R₀ σf σg :=
    { primitive := Pr
      response := r
      gap := hgap
      initialization := fun a => by rw [hzero a,norm_zero];exact hR₀
      upper := Of
      lower := Og
      upper_truth := hft
      lower_truth := hgt }
  refine ⟨hD,F,?_,?_,fun _ _ => rfl⟩
  · apply F.rateProperty_of_original reply
      (physicalOriginalLoss macroN J n D cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν ρ R K) ε rate
    · exact hs
    · intro a x
      change ‖gradient ((Pr a).hyperobjective (r a)) x‖=_
      rw [funext (hmean a)]
      rfl
    · intro Aalg ha
      have ha' := ha
      rw [independentStream_unit] at ha'
      have hh := @hRate inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
        Aalg.Private Aalg.State inferInstance inferInstance Aalg.program Aalg.start Aalg.start_measurable
        Aalg.privateLaw inferInstance ha'
      simpa only [independentStream_unit] using hh
  · intro a coin
    obtain ⟨f,g,hf,hg⟩ := physicalOriginalReply_conservative macroN J n D s cn ratios resolutions hdim hAll hT
      initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn m δ c₀ cend hF a (hExt a)
    refine ⟨f,g,?_,?_⟩
    · intro q
      have he := congrArg Prod.fst (hs a q coin)
      change (Of a).sample q coin=_ at he
      change HasGradientAt f ((Of a).sample q coin) q
      rw [he]
      exact hf q
    · intro q
      have he := congrArg Prod.snd (hs a q coin)
      change (Og a).sample q coin=_ at he
      change HasGradientAt g ((Og a).sample q coin) q
      rw [he]
      exact hg q

end Bilevel.TransportHierarchy
