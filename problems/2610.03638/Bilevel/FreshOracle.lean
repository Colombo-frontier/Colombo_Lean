import Bilevel.StochasticInner
import Mathlib.MeasureTheory.Integral.Prod

/-! A pointwise unbiased bounded-variance sampling interface and its actual
adaptive-query realization with a fresh independent seed. L2 integrability,
the variance bound, and conditional centering are derived by Fubini. -/

noncomputable section
open MeasureTheory

namespace Bilevel.FreshOracle

variable {Query Seed E : Type*} [MeasurableSpace Query] [MeasurableSpace Seed]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The original pointwise SFO mean and variance assumptions. No property of
adaptive queries or conditional expectation is a field of this structure. -/
structure Oracle (ν : Measure Seed) (σ : ℝ) where
  truth : Query → E
  sample : Query → Seed → E
  truth_measurable : Measurable truth
  sample_measurable : Measurable (fun qs : Query × Seed => sample qs.1 qs.2)
  square_integrable : ∀ q, Integrable (fun s => ‖sample q s - truth q‖ ^ 2) ν
  mean : ∀ q, (∫ s, sample q s - truth q ∂ν) = 0
  variance : ∀ q, (∫ s, ‖sample q s - truth q‖ ^ 2 ∂ν) ≤ σ ^ 2

namespace Oracle

variable {ν : Measure Seed} [IsProbabilityMeasure ν] {σ : ℝ}
variable (O : Oracle (Query := Query) (E := E) ν σ)

def error (q : Query) (s : Seed) : E := O.sample q s - O.truth q

omit [CompleteSpace E] [IsProbabilityMeasure ν] in
theorem error_measurable : Measurable (fun qs : Query × Seed => O.error qs.1 qs.2) :=
  O.sample_measurable.sub (O.truth_measurable.comp measurable_fst)

omit [CompleteSpace E] [IsProbabilityMeasure ν] in
theorem error_memLp (q : Query) : MemLp (O.error q) 2 ν := by
  apply (memLp_two_iff_integrable_sq_norm
    ((O.error_measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)).mpr
  exact O.square_integrable q

omit [CompleteSpace E] in
theorem error_integrable (q : Query) : Integrable (O.error q) ν :=
  (O.error_memLp q).integrable (by norm_num)

theorem sample_mean (q : Query) : (∫ s, O.sample q s ∂ν) = O.truth q := by
  have he : (fun s => O.sample q s) = fun s => O.error q s + O.truth q := by
    funext s
    simp [error]
  rw [he, integral_add (O.error_integrable q) (integrable_const _)]
  change (∫ s, O.sample q s - O.truth q ∂ν) + _ = _
  rw [O.mean]
  simp

variable {Past : Type*} [MeasurableSpace Past] {μ : Measure Past} [IsProbabilityMeasure μ]

def adaptiveError (q : Past → Query) (z : Past × Seed) : E := O.error (q z.1) z.2

omit [CompleteSpace E] [IsProbabilityMeasure ν] in
theorem adaptiveError_measurable (q : Past → Query) (hq : Measurable q) :
    Measurable (O.adaptiveError q) :=
  O.error_measurable.comp ((hq.comp measurable_fst).prodMk measurable_snd)

omit [CompleteSpace E] in
theorem adaptiveError_square_integrable (q : Past → Query) (hq : Measurable q) :
    Integrable (fun z => ‖O.adaptiveError q z‖ ^ 2) (μ.prod ν) := by
  have hm := ((O.adaptiveError_measurable q hq).norm.pow_const 2).aestronglyMeasurable (μ := μ.prod ν)
  apply (integrable_prod_iff hm).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun z => O.square_integrable (q z))
  · apply (integrable_const (σ ^ 2)).mono' hm.norm.integral_prod_right'
    filter_upwards [] with z
    have he : (∫ s, ‖‖O.adaptiveError q (z, s)‖ ^ 2‖ ∂ν) =
        ∫ s, ‖O.adaptiveError q (z, s)‖ ^ 2 ∂ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun s => Real.norm_of_nonneg (sq_nonneg _))
    rw [he, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
    exact O.variance (q z)

omit [CompleteSpace E] in
theorem adaptiveError_memLp (q : Past → Query) (hq : Measurable q) :
    MemLp (O.adaptiveError q) 2 (μ.prod ν) :=
  (memLp_two_iff_integrable_sq_norm (O.adaptiveError_measurable q hq).aestronglyMeasurable).mpr
    (O.adaptiveError_square_integrable q hq)

def adaptiveErrorLp (q : Past → Query) (hq : Measurable q) : Lp E 2 (μ.prod ν) :=
  (O.adaptiveError_memLp q hq).toLp _

omit [CompleteSpace E] in
theorem adaptiveErrorLp_coe (q : Past → Query) (hq : Measurable q) :
    (O.adaptiveErrorLp (μ := μ) q hq : Past × Seed → E) =ᵐ[μ.prod ν] O.adaptiveError q :=
  (O.adaptiveError_memLp (μ := μ) q hq).coeFn_toLp

omit [CompleteSpace E] in
theorem adaptiveError_integrable (q : Past → Query) (hq : Measurable q) :
    Integrable (O.adaptiveError q) (μ.prod ν) :=
  (O.adaptiveError_memLp q hq).integrable (by norm_num)

omit [CompleteSpace E] in
theorem adaptiveError_variance (q : Past → Query) (hq : Measurable q) :
    (∫ z, ‖O.adaptiveError q z‖ ^ 2 ∂μ.prod ν) ≤ σ ^ 2 := by
  have hi := O.adaptiveError_square_integrable (μ := μ) q hq
  rw [integral_prod _ hi]
  have hb := integral_mono hi.integral_prod_left (integrable_const (σ ^ 2))
    (fun z => O.variance (q z))
  simpa only [integral_const, measureReal_univ_eq_one, one_smul] using hb

omit [CompleteSpace E] in
theorem adaptiveErrorLp_risk (q : Past → Query) (hq : Measurable q) :
    StochasticInner.risk (O.adaptiveErrorLp (μ := μ) q hq) ≤ σ ^ 2 := by
  have he : StochasticInner.risk (O.adaptiveErrorLp (μ := μ) q hq) =
      ∫ z, ‖O.adaptiveError q z‖ ^ 2 ∂μ.prod ν := by
    apply integral_congr_ae
    filter_upwards [O.adaptiveErrorLp_coe (μ := μ) q hq] with z hz
    rw [hz]
  rw [he]
  exact O.adaptiveError_variance q hq

def pastSpace : MeasurableSpace (Past × Seed) := MeasurableSpace.comap Prod.fst inferInstance

theorem pastSpace_le : pastSpace (Past := Past) (Seed := Seed) ≤
    (inferInstance : MeasurableSpace (Past × Seed)) := measurable_fst.comap_le

omit [CompleteSpace E] in
theorem adaptiveError_setIntegral (q : Past → Query) (hq : Measurable q)
    (s : Set (Past × Seed)) (hs : MeasurableSet[pastSpace] s) :
    (∫ z in s, O.adaptiveError q z ∂μ.prod ν) = 0 := by
  obtain ⟨t, _ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  have he : Prod.fst ⁻¹' t = t ×ˢ (Set.univ : Set Seed) := by ext z; simp
  rw [he, setIntegral_prod _ (O.adaptiveError_integrable q hq).integrableOn]
  simp only [Measure.restrict_univ]
  change (∫ z in t, ∫ s, O.sample (q z) s - O.truth (q z) ∂ν ∂μ) = 0
  simp only [O.mean, integral_zero]

theorem adaptiveErrorLp_condExpL2 (q : Past → Query) (hq : Measurable q) :
    (condExpL2 E ℝ (pastSpace_le (Past := Past) (Seed := Seed))
      (O.adaptiveErrorLp (μ := μ) q hq) : Lp E 2 (μ.prod ν)) = 0 := by
  apply Lp.ext
  refine Lp.ae_eq_of_forall_setIntegral_eq' ℝ pastSpace_le _ _ two_ne_zero ENNReal.coe_ne_top
    (fun s _ hs => integrableOn_condExpL2_of_measure_ne_top pastSpace_le hs.ne _)
    (fun s _ hs => integrableOn_Lp_of_measure_ne_top _ (by norm_num) hs.ne) ?_
    (lpMeas.aestronglyMeasurable _) ?_
  · intro s hs hμs
    rw [integral_condExpL2_eq pastSpace_le _ hs hμs.ne]
    have he := ae_restrict_of_ae (s := s) (O.adaptiveErrorLp_coe (μ := μ) q hq)
    rw [integral_congr_ae he, O.adaptiveError_setIntegral q hq s hs]
    have hz := integral_congr_ae (ae_restrict_of_ae (s := s) (Lp.coeFn_zero E 2 (μ.prod ν)))
    simpa only [Pi.zero_apply, integral_zero] using hz.symm
  · exact aestronglyMeasurable_zero.congr (Lp.coeFn_zero E 2 (μ.prod ν)).symm

end Oracle
end Bilevel.FreshOracle
