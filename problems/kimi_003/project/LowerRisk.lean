import UpperOptimization
import LowerAudit

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Task006.LowerRisk

noncomputable section
variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Conditional averaging against an arbitrary measurable output, restricted
to an observable event. No output-in-span restriction is imposed. -/
theorem event_inner_transport {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (event : Set Ω) (he : MeasurableSet[m] event) (θ C y : Ω → E)
    (hy : StronglyMeasurable[m] y) (hθ : Integrable θ μ)
    (hinner : Integrable (fun ω => inner ℝ (event.indicator y ω) (θ ω)) μ)
    (hCE : μ[θ | m] =ᵐ[μ] C) :
    (∫ ω, event.indicator (fun ω => inner ℝ (θ ω) (y ω)) ω ∂μ) =
      ∫ ω, event.indicator (fun ω => inner ℝ (C ω) (y ω)) ω ∂μ := by
  letI : MeasurableSpace Ω := mΩ
  have h := Task006.Full.predictable_inner_integral (mΩ := mΩ) (m := m) hm (hy.indicator he) hinner hθ
  have hl : (fun ω => inner ℝ (event.indicator y ω) (θ ω)) =
      event.indicator (fun ω => inner ℝ (θ ω) (y ω)) := by
    funext ω
    by_cases hω : ω ∈ event
    · simp only [indicator_of_mem hω,real_inner_comm]
    · simp only [indicator_of_notMem hω,inner_zero_left]
  rw [hl] at h
  apply h.trans
  apply integral_congr_ae
  filter_upwards [hCE] with ω hω
  by_cases heω : ω ∈ event
  · simp only [indicator_of_mem heω,hω,real_inner_comm]
  · simp only [indicator_of_notMem heω,inner_zero_left]

/-- The risk on an observable event follows from the actual conditional mean
and a norm bound on an arbitrary output; no risk bound is assumed. -/
theorem risk_lower_from_conditional_mean {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (event : Set Ω) (he : MeasurableSet[m] event) (θ C y : Ω → E)
    (R slope : ℝ) (hR : 0 ≤ R) (hslope : 0 ≤ slope)
    (hy : StronglyMeasurable[m] y) (hyR : ∀ ω, ‖y ω‖ ≤ R)
    (hθ : Integrable θ μ) (hC : Integrable C μ)
    (hinner : Integrable (fun ω => inner ℝ (event.indicator y ω) (θ ω)) μ)
    (hCE : μ[θ | m] =ᵐ[μ] C)
    (gap : Ω → ℝ) (hgap : Integrable gap μ) (hgap0 : ∀ ω, 0 ≤ gap ω)
    (hagreement : ∀ ω ∈ event, gap ω = slope*(R+inner ℝ (θ ω) (y ω))) :
    slope*R*(μ.real event - ∫ ω, event.indicator (fun ω => ‖C ω‖) ω ∂μ) ≤
      ∫ ω, gap ω ∂μ := by
  classical
  letI : MeasurableSpace Ω := mΩ
  have heΩ : MeasurableSet event := hm event he
  have htransport := event_inner_transport hm event he θ C y hy hθ hinner hCE
  have hiy : Integrable (event.indicator (fun ω => inner ℝ (θ ω) (y ω))) μ := by
    have heq : (fun ω => inner ℝ (event.indicator y ω) (θ ω)) =
        event.indicator (fun ω => inner ℝ (θ ω) (y ω)) := by
      funext ω
      by_cases hω : ω ∈ event <;> simp [hω,real_inner_comm]
    rw [← heq]
    exact hinner
  have hic : Integrable (event.indicator (fun ω => inner ℝ (C ω) (y ω))) μ := by
    apply ((hC.norm).const_mul R).mono'
    · exact (hC.aestronglyMeasurable.inner (hy.mono hm).aestronglyMeasurable).indicator heΩ
    · apply Filter.Eventually.of_forall
      intro ω
      by_cases hω : ω ∈ event
      · rw [indicator_of_mem hω]
        have hb := (norm_inner_le_norm (𝕜 := ℝ) (C ω) (y ω)).trans
          (mul_le_mul_of_nonneg_left (hyR ω) (norm_nonneg (C ω)))
        simpa only [mul_comm R] using hb
      · rw [indicator_of_notMem hω,norm_zero]
        positivity
  have hinorm : Integrable (event.indicator (fun ω => ‖C ω‖)) μ := hC.norm.indicator heΩ
  have hpoint : ∀ ω, -R * event.indicator (fun ω => ‖C ω‖) ω ≤
      event.indicator (fun ω => inner ℝ (C ω) (y ω)) ω := by
    intro ω
    by_cases hω : ω ∈ event
    · simp only [indicator_of_mem hω]
      have hb := (norm_inner_le_norm (𝕜 := ℝ) (C ω) (y ω)).trans
        (mul_le_mul_of_nonneg_left (hyR ω) (norm_nonneg (C ω)))
      rw [Real.norm_eq_abs] at hb
      have hl := (abs_le.mp hb).1
      nlinarith
    · simp only [indicator_of_notMem hω,mul_zero,le_refl]
  have hb := integral_mono (hinorm.const_mul (-R)) hic hpoint
  rw [integral_const_mul] at hb
  let G : Ω → ℝ := fun ω => (slope*R)*event.indicator (fun _ => (1 : ℝ)) ω +
    slope*event.indicator (fun ω => inner ℝ (θ ω) (y ω)) ω
  have hG : Integrable G μ :=
    ((integrable_const (1 : ℝ)).indicator heΩ).const_mul (slope*R) |>.add (hiy.const_mul slope)
  have hp : ∀ ω, G ω ≤ gap ω := by
    intro ω
    by_cases hω : ω ∈ event
    · dsimp only [G]
      simp only [indicator_of_mem hω,hagreement ω hω]
      exact le_of_eq (by ring)
    · simpa only [G,indicator_of_notMem hω,mul_zero,add_zero] using hgap0 ω
  have hg := integral_mono hG hgap hp
  change (∫ ω, (slope*R)*event.indicator (fun _ => (1 : ℝ)) ω +
    slope*event.indicator (fun ω => inner ℝ (θ ω) (y ω)) ω ∂μ) ≤ _ at hg
  rw [integral_add (((integrable_const (1 : ℝ)).indicator heΩ).const_mul (slope*R))
      (hiy.const_mul slope),integral_const_mul,integral_const_mul,
      integral_indicator_const (1 : ℝ) heΩ,htransport] at hg
  simp only [smul_eq_mul,mul_one] at hg
  have hm := mul_le_mul_of_nonneg_left hb hslope
  nlinarith

/-- Event Cauchy--Schwarz, derived from the actual integrable square. -/
theorem event_cauchy_schwarz (event : Set Ω) (he : MeasurableSet event)
    (f : Ω → ℝ) (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω)
    (hf2 : Integrable (fun ω => f ω^2) μ) :
    (∫ ω, event.indicator f ω ∂μ)^2 ≤
      μ.real event * (∫ ω, event.indicator (fun ω => f ω^2) ω ∂μ) := by
  classical
  let X := event.indicator f
  have hmX : Measurable X := hf.indicator he
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω => Set.indicator_nonneg (fun ω _ => hf0 ω) ω
  have hX2 : Integrable (fun ω => X ω^2) μ := by
    have heq : (fun ω => X ω^2) = event.indicator (fun ω => f ω^2) := by
      funext ω
      by_cases hω : ω ∈ event <;> simp [X,hω]
    rw [heq]
    exact hf2.indicator he
  have hLpX : MemLp X 2 μ := (memLp_two_iff_integrable_sq hmX.aestronglyMeasurable).mpr hX2
  have hLpOne : MemLp (event.indicator (fun _ : Ω => (1 : ℝ))) 2 μ :=
    (memLp_const (1 : ℝ)).indicator he
  have hHolder : (2 : ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have hOne_nonneg : ∀ ω, 0 ≤ event.indicator (fun _ : Ω => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : ω ∈ event <;> simp [hω]
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg hHolder
    (Filter.Eventually.of_forall hX0)
    (Filter.Eventually.of_forall hOne_nonneg)
    (by convert hLpX using 1 <;> norm_num)
    (by convert hLpOne using 1 <;> norm_num)
  have hl : (∫ ω, X ω * event.indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ) =
      ∫ ω, X ω ∂μ := by
    apply integral_congr_ae
    filter_upwards with ω
    by_cases hω : ω ∈ event <;> simp [X,hω]
  have hr : (∫ ω, (event.indicator (fun _ : Ω => (1 : ℝ)) ω) ^ (2 : ℝ) ∂μ) = μ.real event := by
    have hpow : (fun ω => (event.indicator (fun _ : Ω => (1 : ℝ)) ω) ^ (2 : ℝ)) =
        event.indicator (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases hω : ω ∈ event <;> simp [hω]
    rw [hpow,integral_indicator_const (1 : ℝ) he]
    simp
  rw [hl,hr] at hCS
  have hCS' : (∫ ω, X ω ∂μ) ≤
      Real.sqrt (∫ ω, X ω^2 ∂μ) * Real.sqrt (μ.real event) := by
    simpa only [Real.sqrt_eq_rpow,Real.rpow_two] using hCS
  have hpow := pow_le_pow_left₀ (integral_nonneg hX0) hCS' 2
  rw [mul_pow,Real.sq_sqrt (integral_nonneg (fun ω => sq_nonneg (X ω))),
    Real.sq_sqrt (show 0 ≤ μ.real event from ENNReal.toReal_nonneg)] at hpow
  have hsq : (fun ω => X ω^2) = event.indicator (fun ω => f ω^2) := by
    funext ω
    by_cases hω : ω ∈ event <;> simp [X,hω]
  rw [hsq] at hpow
  exact hpow.trans_eq (mul_comm _ _)

/-- A direct scalar closing argument with unnormalized event moments. -/
theorem large_dimension_risk_from_event_moments (eps risk a n e : ℝ)
    (heps : 0 < eps) (ha : 1/2 ≤ a) (hn : 0 ≤ n)
    (he : e ≤ 1/3) (hCS : n^2 ≤ a*e)
    (hrisk : 16*eps*(a-n) ≤ risk) : eps < risk := by
  have ha0 : 0 ≤ a := by linarith
  have hCS' : n^2 ≤ a/3 := hCS.trans (by nlinarith)
  have han : 1/16 < a-n := by
    by_contra hh
    have hna : a-1/16 ≤ n := by linarith
    have hs := pow_le_pow_left₀ (by linarith : 0 ≤ a-1/16) hna 2
    have haa := mul_nonneg ha0 (show 0 ≤ a-1/2 by linarith)
    nlinarith
  nlinarith

end
end Task006.LowerRisk
