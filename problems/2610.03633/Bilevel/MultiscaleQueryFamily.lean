import Bilevel.PrimitiveQueryFamily
import Bilevel.MultiscaleJointChannels
import Bilevel.FreshOracleQueryMap

/-! The actual macro-free family in the common original-SFO model.
The same retained Primitive supplies the loss, gap, complete paired oracle,
conservative sample potentials and expected-query lower bound. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory
namespace Bilevel.MultiscaleMean
open PrimitiveGeometry CompensatedMean BorelAdaptive ChiHierarchyHaar ChiHierarchyIndex SingleFrameSource
variable {n dim : ℕ}
  [MeasurableSpace (LowerSpace (EuclideanGaussian.Space dim))]
  [BorelSpace (LowerSpace (EuclideanGaussian.Space dim))]
  [MeasurableSpace (Joint (EuclideanGaussian.Space dim) (LowerSpace (EuclideanGaussian.Space dim)))]
  [BorelSpace (Joint (EuclideanGaussian.Space dim) (LowerSpace (EuclideanGaussian.Space dim)))]

theorem inner_model_family
    (P : Parameters (E:=EuclideanGaussian.Space dim) n)
    (hD : ∀ i : FrameIndex (counts n) 0,chainSize i+1≤dim)
    {μ L ρ Δ C κ ε σf σg cost R₀ : ℝ} (hR₀ : 0≤R₀) (hs : P.β*P.θ≤1)
    (hRate : InnerRateProperty.{0,0} P hD (P.activationProbability σg)
      (P.activationProbability_le_one σg) ε cost)
    (hP : ∀ a,InnerPrimitiveCertificate (P.withFrame (frame hD a (Sum.inl ()))) μ L ρ Δ C κ ε) :
    ∃ F : PrimitiveQuery.Family
      (PrimitiveQuery.Geometry.of (EuclideanGaussian.Space dim) (LowerSpace (EuclideanGaussian.Space dim)))
      (Orientations (counts n) 0 dim) Bool
      (BernoulliOracle.law (P.activationProbability σg) (P.activationProbability_le_one σg))
      μ L ρ Δ R₀ σf σg,
      F.RateProperty ε cost ∧
      (∀ a,(F.instance a).CurvatureBound (C*L*κ^2)) ∧
      (∀ a,(F.instance a).IsConservative) := by
  classical
  choose Of Og hft hgt hfs hgs hsample hsampleC3 using
    fun a => (hP a).full_oracles σf σg hs
  let F : PrimitiveQuery.Family
      (PrimitiveQuery.Geometry.of (EuclideanGaussian.Space dim) (LowerSpace (EuclideanGaussian.Space dim)))
      (Orientations (counts n) 0 dim) Bool
      (BernoulliOracle.law (P.activationProbability σg) (P.activationProbability_le_one σg))
      μ L ρ Δ R₀ σf σg := {
    primitive := fun a => (hP a).primitive
    response := fun a => (hP a).response
    gap := fun a => (hP a).gap
    initialization := fun a => by rw [(hP a).origin,norm_zero];exact hR₀
    upper := fun a => (Of a).reparametrize (unpackQuery (E:=EuclideanGaussian.Space dim)) (unpackQuery_measurable (E:=EuclideanGaussian.Space dim))
    lower := fun a => (Og a).reparametrize (unpackQuery (E:=EuclideanGaussian.Space dim)) (unpackQuery_measurable (E:=EuclideanGaussian.Space dim))
    upper_truth := fun a q => hft a (unpackQuery q)
    lower_truth := fun a q => hgt a (unpackQuery q) }
  let reply := fun a => jointOriginalReply (P.withFrame (frame hD a (Sum.inl ()))) (P.activationProbability σg)
  have hr (a) (q) (c) : F.reply a q c=reply a q c := by
    change ((Of a).sample (unpackQuery q) c,(Og a).sample (unpackQuery q) c)=_
    rw [hfs,hgs]
    rfl
  have hl (a) (x) : F.loss a x=innerFrameLoss P hD a x := by
    change ‖gradient ((hP a).primitive.hyperobjective (hP a).response) x‖=_
    rw [(hP a).mean_eq]
    rfl
  have hr' : F.reply=reply := funext (fun a => funext (fun q => funext (hr a q)))
  have hl' : F.loss=innerFrameLoss P hD := funext (fun a => funext (hl a))
  refine ⟨F,?_,?_,?_⟩
  · intro A hacc
    have hacc' := hacc
    rw [hr',hl'] at hacc'
    obtain ⟨a,ha⟩ := inner_rate_joint_channel P hD (P.activationProbability σg)
      (P.activationProbability_le_one σg) ε cost hRate A.program A.start A.start_measurable A.privateLaw hacc'
    refine ⟨a,?_⟩
    rw [hr']
    exact ha
  · intro a
    exact (hP a).curvature
  · intro a c
    obtain ⟨f,g,hf,hg⟩ := jointOriginalReply_conservative
      (P.withFrame (frame hD a (Sum.inl ()))) (P.activationProbability σg) c
    refine ⟨f,g,?_,?_⟩
    · intro q
      have he := congrArg Prod.fst (hr a q c)
      change HasGradientAt f (F.reply a q c).1 q
      rw [he]
      exact hf q
    · intro q
      have he := congrArg Prod.snd (hr a q c)
      change HasGradientAt g (F.reply a q c).2 q
      rw [he]
      exact hg q

end Bilevel.MultiscaleMean
