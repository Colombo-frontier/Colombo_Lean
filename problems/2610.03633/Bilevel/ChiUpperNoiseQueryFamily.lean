import Bilevel.ChiUpperNoiseQueryGeometry
import Bilevel.ChiUpperNoiseRateProperty
import Bilevel.PrimitiveQueryFamilyRealization

/-! Same-Primitive upper-noise family in the actual query model. The public
lower oracle is exact and the complete upper sample remains conservative. -/
noncomputable section
open MeasureTheory
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  ChiPrefixEvaluation PrimitiveGeometry ChiExtensionCalibration ChiUpperNoise PrimitiveQuery
set_option autoImplicit false
set_option maxHeartbeats 1200000
variable (macroN dim : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) 0,chainSize i+1≤dim)
  (sc : Scale) (weight : ℕ → ℝ) (ζ CR Km : ℝ) (rad R : ℕ → ℝ) (K ε : ℝ)

theorem upper_noise_query_family
    (μ L ρ Δ R₀ σf σg B rate : ℝ) (hR₀ : 0≤R₀) (hB : 0<B)
    (P : Orientations (sourceCounts macroN cn ratios resolutions) 0 dim →
      Model.Primitive (X:=UpperNoiseOutput dim) (Y:=Blocks 1 (EuclideanGaussian.Space dim)) μ L L L ρ)
    (r : ∀ a,(P a).Response)
    (hgap : ∀ a,Nonempty ((P a).GapCertificate (r a) 0 Δ))
    (hzero : ∀ a,(r a).y 0=0)
    (hmean : ∀ a x,(P a).hyperobjective (r a) x=jointOuter 1
      (sourceCanonicalMacro macroN 0 dim cn ratios resolutions hAll a sc Km) (sc.curvature/24)
      (sourceCanonicalGeometry macroN 0 dim cn ratios resolutions hdim a sc weight 3 1 ζ CR) rad R 0 K x)
    (hFull : ∀ a,HasUpperNoiseFullOracle macroN dim cn ratios resolutions hdim hAll sc weight ζ CR Km rad R μ L ρ B a (P a))
    (hRate : UpperNoiseRateProperty.{0,0} macroN dim cn ratios resolutions hdim hAll sc weight ζ CR Km rad R K ε μ L
      (BernoulliOracle.probability B σf) (BernoulliOracle.probability_le_one hB) rate) :
    ∃ hD : 0<dim,
    ∃ F : PrimitiveQuery.Family (upperNoiseGeometry dim hD)
      (Orientations (sourceCounts macroN cn ratios resolutions) 0 dim) Bool
      (BernoulliOracle.law (BernoulliOracle.probability B σf) (BernoulliOracle.probability_le_one hB)) μ L ρ Δ R₀ σf σg,
      F.RateProperty ε rate ∧ (∀ a,(F.instance a).IsConservative) ∧
      ∀ a x,(F.primitive a).hyperobjective (F.response a) x=(P a).hyperobjective (r a) x := by
  classical
  have hD : 0<dim := lt_of_lt_of_le (Nat.succ_pos _) (hdim 0)
  let G := upperNoiseGeometry dim hD
  letI : MeasurableSpace (UpperNoiseOutput dim) := G.measurableX
  letI : BorelSpace (UpperNoiseOutput dim) := G.borelX
  letI : MeasurableSpace (Blocks 1 (EuclideanGaussian.Space dim)) := G.measurableY
  letI : BorelSpace (Blocks 1 (EuclideanGaussian.Space dim)) := G.borelY
  letI : MeasurableSpace (UpperNoiseQuery dim) := G.measurableQuery
  letI : BorelSpace (UpperNoiseQuery dim) := G.borelQuery
  let reply := sourceUpperNoiseJoint macroN dim cn ratios resolutions hdim hAll sc weight 3 1 ζ CR Km
    (sc.curvature/24) rad R (publicLower μ L) (BernoulliOracle.probability B σf)
  have horacles (a : Orientations (sourceCounts macroN cn ratios resolutions) 0 dim) :
      ∃ Of : FreshOracle.Oracle (Query:=G.Query) (E:=G.Query)
        (BernoulliOracle.law (BernoulliOracle.probability B σf) (BernoulliOracle.probability_le_one hB)) σf,
      ∃ Og : FreshOracle.Oracle (Query:=G.Query) (E:=G.Query)
        (BernoulliOracle.law (BernoulliOracle.probability B σf) (BernoulliOracle.probability_le_one hB)) σg,
        (∀ q,Of.truth q=pack ((P a).fx q.fst q.snd) ((P a).fy q.fst q.snd)) ∧
        (∀ q,Og.truth q=pack ((P a).gx q.fst q.snd) ((P a).gy q.fst q.snd)) ∧
        ∀ q c,(Of.sample q c,Og.sample q c)=reply a q c := by
    obtain ⟨hb,Of,Og,hf,hg,hs⟩ := hFull a σf σg
    exact ⟨Of,Og,hf,hg,hs⟩
  choose Of Og hft hgt hs using horacles
  let F : PrimitiveQuery.Family G
      (Orientations (sourceCounts macroN cn ratios resolutions) 0 dim) Bool
      (BernoulliOracle.law (BernoulliOracle.probability B σf) (BernoulliOracle.probability_le_one hB)) μ L ρ Δ R₀ σf σg :=
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
      (sourceOriginalLoss macroN 0 dim cn ratios resolutions hdim hAll sc weight 3 1 ζ CR Km
        1 (sc.curvature/24) rad R 0 K) ε rate
    · exact hs
    · intro a x
      change ‖gradient ((P a).hyperobjective (r a)) x‖=_
      rw [funext (hmean a)]
      rfl
    · intro A ha
      exact @hRate inferInstance inferInstance inferInstance inferInstance
        A.Private A.State inferInstance inferInstance A.program A.start A.start_measurable
        A.privateLaw inferInstance ha
  · intro a coin
    obtain ⟨f,g,hf,hg⟩ := sourceUpperNoiseJoint_conservative macroN dim cn ratios resolutions hdim hAll sc weight
      ζ CR Km rad R μ L (BernoulliOracle.probability B σf) a coin
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

end Bilevel.ChiHierarchyHaar
