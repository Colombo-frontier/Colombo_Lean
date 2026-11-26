import Bilevel.FreshOracle
import Bilevel.BorelAdaptiveProductFreshness
import Bilevel.PolishedHistoryStationaryStopping
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! Fresh pointwise SFO assumptions imply actual conditional expectations
relative to all private randomness and past draws. No conditional moment or
accuracy conclusion is an assumption. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.PolishedHistory
set_option autoImplicit false
set_option maxHeartbeats 1400000
variable {Ω P C Q E : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace P]
  [MeasurableSpace C] [MeasurableSpace Q]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {π : Measure P} [IsProbabilityMeasure π]
  {ν : Measure C} [IsProbabilityMeasure ν] {σ : ℝ}

omit [CompleteSpace E] [IsProbabilityMeasure μ] [IsProbabilityMeasure π] [IsProbabilityMeasure ν] in
private theorem pair_setIntegral (past : Ω → P) (draw : Ω → C)
    (hp : MeasurePreserving (fun ω => (past ω,draw ω)) μ (π.prod ν))
    (f : P × C → E) (hf : Measurable f) (t : Set P) (ht : MeasurableSet t) :
    (∫ ω in past ⁻¹' t,f (past ω,draw ω) ∂μ)=∫ z in t ×ˢ Set.univ,f z ∂π.prod ν := by
  have ha : AEStronglyMeasurable f (μ.map (fun ω => (past ω,draw ω))) := by
    rw [hp.map_eq]
    exact hf.aestronglyMeasurable
  have h := setIntegral_map (ht.prod MeasurableSet.univ) ha hp.measurable.aemeasurable
  rw [hp.map_eq] at h
  have he : (fun ω => (past ω,draw ω)) ⁻¹' (t ×ˢ Set.univ)=past ⁻¹' t := by ext ω;simp
  rw [he] at h
  exact h.symm

/-- Actual pre-query conditional moments for an independent fresh draw.
The past may contain an entire private seed and every earlier observation. -/
theorem fresh_conditional_moments (O : FreshOracle.Oracle (Query:=Q) (E:=E) ν σ)
    (past : Ω → P) (draw : Ω → C)
    (hp : MeasurePreserving (fun ω => (past ω,draw ω)) μ (π.prod ν))
    (query : P → Q) (hq : Measurable query) :
    Integrable (fun ω => ‖O.error (query (past ω)) (draw ω)‖^2) μ ∧
    (μ[fun ω => O.error (query (past ω)) (draw ω) | MeasurableSpace.comap past inferInstance] =ᵐ[μ] 0) ∧
    (∀ᵐ ω ∂μ,μ[fun ω => ‖O.error (query (past ω)) (draw ω)‖^2 |
      MeasurableSpace.comap past inferInstance] ω≤σ^2) := by
  have hpast : Measurable past := measurable_fst.comp hp.measurable
  have hInformation : (MeasurableSpace.comap past (inferInstance : MeasurableSpace P))≤mΩ := hpast.comap_le
  let err : P × C → E := O.adaptiveError query
  have herr : Measurable err := O.adaptiveError_measurable query hq
  have hi := O.adaptiveError_integrable (μ:=π) query hq
  have hs := O.adaptiveError_square_integrable (μ:=π) query hq
  have herror : Integrable (fun ω => err (past ω,draw ω)) μ :=
    (hp.integrable_comp herr.aestronglyMeasurable).mpr hi
  have hsquare : Integrable (fun ω => ‖err (past ω,draw ω)‖^2) μ :=
    (hp.integrable_comp (herr.norm.pow_const 2).aestronglyMeasurable).mpr hs
  refine ⟨hsquare,?_,?_⟩
  · apply Filter.EventuallyEq.symm
    apply ae_eq_condExp_of_forall_setIntegral_eq (μ:=μ) (m:=(MeasurableSpace.comap past (inferInstance : MeasurableSpace P))) (m₀:=mΩ) hInformation herror
    · intro t _ _
      exact (integrable_zero Ω E μ).integrableOn
    · intro t ht _
      obtain ⟨s,hsm,rfl⟩ := MeasurableSpace.measurableSet_comap.mp ht
      simp only [Pi.zero_apply,integral_zero]
      rw [pair_setIntegral past draw hp err herr s hsm]
      have he : s ×ˢ (Set.univ : Set C)=Prod.fst ⁻¹' s := by ext z;simp
      rw [he]
      exact (O.adaptiveError_setIntegral (μ:=π) query hq _
        (MeasurableSpace.measurableSet_comap.mpr ⟨s,hsm,rfl⟩)).symm
    · exact aestronglyMeasurable_zero
  · let variance : P → ℝ := fun p => ∫ c,‖O.error (query p) c‖^2 ∂ν
    have hvs : StronglyMeasurable variance :=
      (herr.norm.pow_const 2).stronglyMeasurable.integral_prod_right'
    have hv0 (p : P) : 0≤variance p := integral_nonneg (fun _ => sq_nonneg _)
    have hvb (p : P) : variance p≤σ^2 := O.variance (query p)
    have hvint : Integrable (fun ω => variance (past ω)) μ := by
      apply (integrable_const (σ^2)).mono' (hvs.comp_measurable hpast).aestronglyMeasurable
      exact Filter.Eventually.of_forall (fun ω => by
        change |variance (past ω)|≤σ^2
        rw [abs_of_nonneg (hv0 _)]
        exact hvb _)
    have hvCE : (fun ω => variance (past ω)) =ᵐ[μ]
        μ[fun ω => ‖err (past ω,draw ω)‖^2 | (MeasurableSpace.comap past (inferInstance : MeasurableSpace P))] := by
      apply ae_eq_condExp_of_forall_setIntegral_eq (μ:=μ) (m:=(MeasurableSpace.comap past (inferInstance : MeasurableSpace P))) (m₀:=mΩ) hInformation hsquare
      · intro t _ _
        exact hvint.integrableOn
      · intro t ht _
        obtain ⟨s,hsm,rfl⟩ := MeasurableSpace.measurableSet_comap.mp ht
        have hfst : MeasurePreserving (Prod.fst : P × C → P) (π.prod ν) π :=
          ⟨measurable_fst,by simp only [Measure.map_fst_prod,measure_univ,one_smul]⟩
        have hpm : MeasurePreserving past μ π := hfst.comp hp
        have hga : AEStronglyMeasurable variance (μ.map past) := by
          rw [hpm.map_eq]
          exact hvs.aestronglyMeasurable
        have hleft := setIntegral_map hsm hga hpm.measurable.aemeasurable
        rw [hpm.map_eq] at hleft
        rw [← hleft,pair_setIntegral past draw hp (fun z => ‖err z‖^2) (herr.norm.pow_const 2) s hsm,
          setIntegral_prod _ hs.integrableOn]
        simp only [Measure.restrict_univ]
        rfl
      · exact (hvs.comp_measurable (show @Measurable Ω P (MeasurableSpace.comap past (inferInstance : MeasurableSpace P)) _ past from Measurable.of_comap_le le_rfl)).aestronglyMeasurable
    filter_upwards [hvCE] with ω hω
    change μ[fun ω => ‖err (past ω,draw ω)‖^2 | (MeasurableSpace.comap past (inferInstance : MeasurableSpace P))] ω≤σ^2
    rw [← hω]
    exact hvb _

end Bilevel.PolishedHistory
