import Bilevel.ChiQueryGeometry
import Bilevel.ChiCanonicalReplyConservative
import Bilevel.ChiExpectedRateProperty
import Bilevel.PrimitiveQueryFamilyRealization

/-! The same canonical Primitive, response and certified full original oracle
form an admissible family in the common finite-dimensional query model. -/
noncomputable section
open MeasureTheory
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  ChiPrefixEvaluation PrimitiveGeometry ChiExtension ChiExtensionCalibration PartialLegendre ChiUpper
  PrimitiveQuery
set_option autoImplicit false
set_option maxHeartbeats 1200000
variable {macroN J dim : ℕ} {cn : ℝ} {ratios resolutions : ℕ → ℝ}
  {hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim}
  {hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤dim}
  {sc : Scale} {weight : ℕ → ℝ} {ζ CR Km : ℝ} {hJ : 1≤J}
  {v : ℝ} {rad R : ℕ → ℝ} {L K ε : ℝ}
  (H : CanonicalQueryCertificate macroN J dim cn ratios resolutions hdim hAll sc weight ζ CR Km hJ v rad R L K ε)

theorem CanonicalQueryCertificate.query_family
    (μ ρ Δ R₀ σf σg B rate : ℝ) (hR₀ : 0≤R₀) (hB : 0<B)
    (P : Orientations (sourceCounts macroN cn ratios resolutions) J dim →
      Model.Primitive (X:=CanonicalX J dim) (Y:=CanonicalY J dim) μ L L L ρ)
    (r : ∀ a,(P a).Response)
    (hgap : ∀ a,Nonempty ((P a).GapCertificate (r a) 0 Δ))
    (hzero : ∀ a,(r a).y 0=0)
    (hmean : ∀ a x,(P a).hyperobjective (r a) x=jointOuter (J+1)
      (sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a sc Km) (sc.curvature/24)
      (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a sc weight 3 1 ζ CR) rad R J K x)
    (hFull : ∀ a,H.HasFullOracle μ ρ B a (P a))
    (hRate : CanonicalQueryCertificate.RateProperty.{0,0} H μ (BernoulliOracle.probability B σg) (BernoulliOracle.probability_le_one hB) rate) :
    ∃ F : PrimitiveQuery.Family (canonicalGeometry J dim hJ)
      (Orientations (sourceCounts macroN cn ratios resolutions) J dim) Bool
      (BernoulliOracle.law (BernoulliOracle.probability B σg) (BernoulliOracle.probability_le_one hB)) μ L ρ Δ R₀ σf σg,
      F.RateProperty ε rate ∧ (∀ a,(F.instance a).IsConservative) ∧
      ∀ a x,(F.primitive a).hyperobjective (F.response a) x=(P a).hyperobjective (r a) x := by
  classical
  let G := canonicalGeometry J dim hJ
  letI : MeasurableSpace (CanonicalX J dim) := G.measurableX
  letI : BorelSpace (CanonicalX J dim) := G.borelX
  letI : MeasurableSpace (CanonicalY J dim) := G.measurableY
  letI : BorelSpace (CanonicalY J dim) := G.borelY
  letI : MeasurableSpace (CanonicalQ J dim) := G.measurableQuery
  letI : BorelSpace (CanonicalQ J dim) := G.borelQuery
  letI : MeasurableSpace (Joint (EuclideanGaussian.Space dim) (CanonicalY J dim)) := borel _
  letI : BorelSpace (Joint (EuclideanGaussian.Space dim) (CanonicalY J dim)) := ⟨rfl⟩
  have horacles (a : Orientations (sourceCounts macroN cn ratios resolutions) J dim) :
      ∃ Of : FreshOracle.Oracle (Query:=G.Query) (E:=G.Query)
        (BernoulliOracle.law (BernoulliOracle.probability B σg) (BernoulliOracle.probability_le_one hB)) σf,
      ∃ Og : FreshOracle.Oracle (Query:=G.Query) (E:=G.Query)
        (BernoulliOracle.law (BernoulliOracle.probability B σg) (BernoulliOracle.probability_le_one hB)) σg,
        (∀ q,Of.truth q=pack ((P a).fx q.fst q.snd) ((P a).fy q.fst q.snd)) ∧
        (∀ q,Og.truth q=pack ((P a).gx q.fst q.snd) ((P a).gy q.fst q.snd)) ∧
        ∀ q c,(Of.sample q c,Og.sample q c)=H.reply μ (BernoulliOracle.probability B σg) a q c := by
    obtain ⟨hb,Of,Og,hf,hg,hs⟩ := hFull a σf σg
    exact ⟨Of,Og,hf,hg,hs⟩
  choose Of Og hft hgt hs using horacles
  let F : PrimitiveQuery.Family G
      (Orientations (sourceCounts macroN cn ratios resolutions) J dim) Bool
      (BernoulliOracle.law (BernoulliOracle.probability B σg) (BernoulliOracle.probability_le_one hB)) μ L ρ Δ R₀ σf σg :=
    { primitive := P
      response := r
      gap := hgap
      initialization := fun a => by rw [hzero a,norm_zero];exact hR₀
      upper := Of
      lower := Og
      upper_truth := hft
      lower_truth := hgt }
  refine ⟨F,?_,?_,fun _ _ => rfl⟩
  · apply F.rateProperty_of_original (H.reply μ (BernoulliOracle.probability B σg))
      (sourceOriginalLoss macroN J dim cn ratios resolutions hdim hAll sc weight 3 1 ζ CR Km
        (J+1) (sc.curvature/24) rad R J K) ε rate
    · exact hs
    · intro a x
      change ‖gradient ((P a).hyperobjective (r a)) x‖=_
      rw [funext (hmean a)]
      rfl
    · intro A ha
      exact @hRate inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance inferInstance inferInstance
        A.Private A.State inferInstance inferInstance A.program A.start A.start_measurable
        A.privateLaw inferInstance ha
  · intro a coin
    obtain ⟨f,g,hf,hg⟩ := H.reply_conservative μ (BernoulliOracle.probability B σg) a coin
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
