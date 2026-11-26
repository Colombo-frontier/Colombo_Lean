import SecondOrder.KernelRelativeEntropy

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal ProbabilityTheory

namespace SecondOrder
noncomputable section
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace.CountablyGenerated β]
  {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {K Q : Kernel α β} [IsMarkovKernel K] [IsMarkovKernel Q]

theorem compProd_withDensity_left (ν : Measure α) [IsProbabilityMeasure ν]
    (Q : Kernel α β) [IsMarkovKernel Q] (f : α → ℝ≥0∞) (hf : Measurable f)
    [IsFiniteMeasure (ν.withDensity f)] :
    (ν.withDensity f) ⊗ₘ Q = (ν ⊗ₘ Q).withDensity (fun z => f z.1) := by
  ext s hs
  have hm : Measurable (s.indicator (fun z : α × β => f z.1)) :=
    (hf.comp measurable_fst).indicator hs
  rw [Measure.compProd_apply hs,withDensity_apply _ hs,← lintegral_indicator hs,
    Measure.lintegral_compProd hm,
    lintegral_withDensity_eq_lintegral_mul ν hf (Q.measurable_kernel_prodMk_left hs)]
  apply lintegral_congr_ae
  filter_upwards [] with a
  change f a*Q a (Prod.mk a ⁻¹' s) = ∫⁻ b, s.indicator (fun z => f z.1) (a,b) ∂Q a
  have he : (fun b => s.indicator (fun z => f z.1) (a,b)) =
      (Prod.mk a ⁻¹' s).indicator (fun _ => f a) := rfl
  rw [he,lintegral_indicator_const (hs.preimage measurable_prodMk_left)]

theorem compProd_eq_withDensity_product (hac : μ ≪ ν) (hKQ : ∀ a, K a ≪ Q a) :
    μ ⊗ₘ K = (ν ⊗ₘ Q).withDensity
      (fun z => μ.rnDeriv ν z.1*K.rnDeriv Q z.1 z.2) := by
  have he : ν.withDensity (μ.rnDeriv ν) = μ := μ.withDensity_rnDeriv_eq ν hac
  haveI : IsFiniteMeasure (ν.withDensity (μ.rnDeriv ν)) := he ▸ inferInstance
  have hb : μ ⊗ₘ Q = (ν ⊗ₘ Q).withDensity (fun z => μ.rnDeriv ν z.1) := by
    rw [← compProd_withDensity_left ν Q _ (Measure.measurable_rnDeriv μ ν),he]
  rw [compProd_eq_withDensity_kernel μ hKQ,hb]
  exact (withDensity_mul (ν ⊗ₘ Q)
    (f := fun z : α × β => μ.rnDeriv ν z.1)
    (g := fun z : α × β => K.rnDeriv Q z.1 z.2)
    ((Measure.measurable_rnDeriv μ ν).comp measurable_fst) (K.measurable_rnDeriv Q)).symm

theorem compProd_llr_chain (hac : μ ≪ ν) (hKQ : ∀ a, K a ≪ Q a) :
    llr (μ ⊗ₘ K) (ν ⊗ₘ Q) =ᵐ[μ ⊗ₘ K]
      (fun z => llr μ ν z.1+kernelLogLikelihood K Q z.1 z.2) := by
  have hj : μ ⊗ₘ K ≪ ν ⊗ₘ Q := hac.compProd (Filter.Eventually.of_forall hKQ)
  have hr : (μ ⊗ₘ K).rnDeriv (ν ⊗ₘ Q) =ᵐ[ν ⊗ₘ Q]
      (fun z => μ.rnDeriv ν z.1*K.rnDeriv Q z.1 z.2) := by
    rw [compProd_eq_withDensity_product hac hKQ]
    exact (ν ⊗ₘ Q).rnDeriv_withDensity
      (((Measure.measurable_rnDeriv μ ν).comp measurable_fst).mul (K.measurable_rnDeriv Q))
  have hp : ∀ᵐ a ∂μ, 0 < (μ.rnDeriv ν a).toReal := by
    filter_upwards [Measure.rnDeriv_pos hac,hac.ae_le (Measure.rnDeriv_ne_top μ ν)] with a ha ht
    exact ENNReal.toReal_pos ha.ne' ht
  have hp' : ∀ᵐ z ∂μ ⊗ₘ K, 0 < (μ.rnDeriv ν z.1).toReal :=
    Measure.ae_compProd_of_ae_ae (measurableSet_lt measurable_const
      (((Measure.measurable_rnDeriv μ ν).comp measurable_fst).ennreal_toReal))
      (hp.mono (fun a ha => Filter.Eventually.of_forall (fun _ => ha)))
  have hk' : ∀ᵐ z ∂μ ⊗ₘ K, 0 < (K.rnDeriv Q z.1 z.2).toReal :=
    Measure.ae_compProd_of_ae_ae (measurableSet_lt measurable_const
      (K.measurable_rnDeriv Q).ennreal_toReal) (Filter.Eventually.of_forall
      (fun a => Kernel.rnDeriv_toReal_pos (hKQ a)))
  filter_upwards [hj.ae_le hr,hp',hk'] with z hz hb hk
  simp only [llr_def,kernelLogLikelihood,hz,ENNReal.toReal_mul,Real.log_mul hb.ne' hk.ne']

theorem compProd_llr_fst_integrable (hint : Integrable (llr μ ν) μ) :
    Integrable (fun z : α × β => llr μ ν z.1) (μ ⊗ₘ K) := by
  apply (Measure.integrable_compProd_iff ((measurable_llr μ ν).comp measurable_fst).aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun a => ?_), ?_⟩
  · exact integrable_const (llr μ ν a)
  simpa using hint.norm

/-- Chain rule for arbitrary response kernels with a bounded conditional KL.
The history laws may differ, as required by an adaptive recursion. -/
theorem klDiv_compProd_chain (hfin : klDiv μ ν ≠ ∞) {C : ℝ} (hC : 0 ≤ C)
    (hKL : ∀ a, klDiv (K a) (Q a) ≤ ENNReal.ofReal C) :
    klDiv (μ ⊗ₘ K) (ν ⊗ₘ Q) = klDiv μ ν+
      ENNReal.ofReal (∫ a, (klDiv (K a) (Q a)).toReal ∂μ) := by
  have hac := (klDiv_ne_top_iff.mp hfin).1
  have hKQ (a : α) : K a ≪ Q a :=
    (klDiv_ne_top_iff.mp (lt_of_le_of_lt (hKL a) ENNReal.ofReal_lt_top).ne).1
  have hi₀ := compProd_llr_fst_integrable (K := K) (klDiv_ne_top_iff.mp hfin).2
  have hi₁ := kernelLogLikelihood_compProd_integrable μ hC hKL
  change Integrable (fun z : α × β => kernelLogLikelihood K Q z.1 z.2) (μ ⊗ₘ K) at hi₁
  have he := compProd_llr_chain hac hKQ
  have hi := (hi₀.add hi₁).congr he.symm
  rw [klDiv_of_ac_of_integrable (hac.compProd (Filter.Eventually.of_forall hKQ)) hi,
    integral_congr_ae he,integral_add hi₀ hi₁,
    Measure.integral_compProd hi₀,Measure.integral_compProd hi₁]
  simp only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul,
    add_sub_cancel_right]
  have he₀ : (∫ a, llr μ ν a ∂μ) = (klDiv μ ν).toReal :=
    (toReal_klDiv_of_measure_eq hac (by simp)).symm
  have he₁ : (∫ a, ∫ b, kernelLogLikelihood K Q a b ∂K a ∂μ) =
      ∫ a, (klDiv (K a) (Q a)).toReal ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with a
    exact kernelLogLikelihood_integral (hKQ a)
  change ENNReal.ofReal ((∫ a, llr μ ν a ∂μ)+(∫ a, ∫ b, kernelLogLikelihood K Q a b ∂K a ∂μ)) = _
  rw [he₀,he₁,ENNReal.ofReal_add ENNReal.toReal_nonneg
    (integral_nonneg (fun _ => ENNReal.toReal_nonneg)),ENNReal.ofReal_toReal hfin]

theorem klDiv_compProd_chain_le (hfin : klDiv μ ν ≠ ∞) {C : ℝ} (hC : 0 ≤ C)
    (hKL : ∀ a, klDiv (K a) (Q a) ≤ ENNReal.ofReal C) :
    klDiv (μ ⊗ₘ K) (ν ⊗ₘ Q) ≤ klDiv μ ν+ENNReal.ofReal C := by
  rw [klDiv_compProd_chain hfin hC hKL]
  apply add_le_add_left
  rw [← klDiv_compProd_same_left μ hC hKL]
  exact klDiv_compProd_same_left_le μ hC hKL

end
end SecondOrder
