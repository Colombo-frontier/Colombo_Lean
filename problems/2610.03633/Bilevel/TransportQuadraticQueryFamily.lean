import Bilevel.TransportQuadraticQueryGeometry
import Bilevel.TransportQuadraticExpectedProperty
import Bilevel.PrimitiveQueryFamilyRealization

/-! Actual physical quadratic transport as a common-model hard family. The
Unit seed stream, paired exact gradients and physical output are unchanged. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  ChiExtensionCalibration EndpointTransportResponse PrimitiveGeometry PrimitiveQuery
set_option autoImplicit false
set_option maxHeartbeats 1200000
variable (macroN n D : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) 0,chainSize i+1≤D)
  (hT : capacity (sourceCounts macroN cn ratios resolutions) 1 0≤D)
  (sc : Scale) (weight : ℕ → ℝ) (ζ CR Km : ℝ) (rad R : ℕ → ℝ) (K ε : ℝ)

theorem quadratic_query_family
    (μ L ρ Δ R₀ σf σg δ c rate : ℝ) (hR₀ : 0≤R₀)
    (P : PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D →
      Model.Primitive (X:=QuadraticOutput D) (Y:=Physical n D) μ L L L ρ)
    (r : ∀ a,(P a).Response)
    (hgap : ∀ a,Nonempty ((P a).GapCertificate (r a) 0 Δ))
    (hzero : ∀ a,(r a).y 0=0)
    (hmean : ∀ a x,(P a).hyperobjective (r a) x=jointOuter 1
      (sourcePhysicalMacro macroN 0 n D cn ratios resolutions hAll a sc Km) (sc.curvature/24)
      (sourcePhysicalGeometry macroN 0 n D cn ratios resolutions hdim hT a sc weight 3 1 ζ CR) rad R 0 K (oneBlockCoordinates x))
    (hFull : ∀ a,HasQuadraticFullOracle macroN n D cn ratios resolutions hdim hAll hT sc weight ζ CR Km rad R μ L ρ δ c a (P a))
    (hRate : QuadraticRateProperty macroN n D cn ratios resolutions hdim hAll hT sc weight ζ CR Km rad R K ε δ c rate) :
    ∃ hD : 0<D,
    ∃ F : PrimitiveQuery.Family (quadraticGeometry n D hD)
      (PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D) Unit (Measure.dirac ()) μ L ρ Δ R₀ σf σg,
      F.RateProperty ε rate ∧ (∀ a,(F.instance a).IsConservative) ∧
      ∀ a x,(F.primitive a).hyperobjective (F.response a) x=(P a).hyperobjective (r a) x := by
  classical
  have hD : 0<D := lt_of_lt_of_le (Nat.succ_pos _) (hdim 0)
  let G := quadraticGeometry n D hD
  letI : MeasurableSpace (QuadraticOutput D) := G.measurableX
  letI : BorelSpace (QuadraticOutput D) := G.borelX
  letI : MeasurableSpace (Physical n D) := G.measurableY
  letI : BorelSpace (Physical n D) := G.borelY
  letI : MeasurableSpace (QuadraticQuery n D) := G.measurableQuery
  letI : BorelSpace (QuadraticQuery n D) := G.borelQuery
  let reply := fun a q (_ : Unit) => quadraticOriginalReply macroN n D cn ratios resolutions hdim hAll hT
    sc weight 3 1 ζ CR Km (sc.curvature/24) (rad 0) (R 0) δ c a q
  have horacles (a : PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D) :
      ∃ Of : FreshOracle.Oracle (Query:=G.Query) (E:=G.Query) (Measure.dirac ()) σf,
      ∃ Og : FreshOracle.Oracle (Query:=G.Query) (E:=G.Query) (Measure.dirac ()) σg,
        (∀ q,Of.truth q=pack ((P a).fx q.fst q.snd) ((P a).fy q.fst q.snd)) ∧
        (∀ q,Og.truth q=pack ((P a).gx q.fst q.snd) ((P a).gy q.fst q.snd)) ∧
        ∀ q coin,(Of.sample q coin,Og.sample q coin)=reply a q coin := hFull a σf σg
  choose Of Og hft hgt hs using horacles
  let F : PrimitiveQuery.Family G
      (PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D) Unit (Measure.dirac ()) μ L ρ Δ R₀ σf σg :=
    { primitive := P
      response := r
      gap := hgap
      initialization := fun a => by rw [hzero a,norm_zero];exact hR₀
      upper := Of
      lower := Og
      upper_truth := hft
      lower_truth := hgt }
  refine ⟨hD,F,?_,?_,fun _ _ => rfl⟩
  · apply F.rateProperty_of_original reply
      (quadraticOriginalLoss macroN n D cn ratios resolutions hdim hAll hT sc weight 3 1 ζ CR Km
        (sc.curvature/24) rad R K) ε rate
    · exact hs
    · intro a x
      change ‖gradient ((P a).hyperobjective (r a)) x‖=_
      rw [funext (hmean a)]
      exact oneBlock_gradient_norm _ x ((jointOuter_contDiff 1 _ _ _ rad R 0 K 1).differentiable (by norm_num) _)
    · intro A ha
      have ha' := ha
      rw [independentStream_unit] at ha'
      have hh := @hRate inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
        A.Private A.State inferInstance inferInstance A.program A.start A.start_measurable
        A.privateLaw inferInstance ha'
      simpa only [independentStream_unit] using hh
  · intro a coin
    obtain ⟨f,g,hf,hg⟩ := quadraticOriginalReply_conservative macroN n D cn ratios resolutions hdim hAll hT
      sc weight ζ CR Km rad R δ c a
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
