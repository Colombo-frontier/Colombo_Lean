import GaussianProductKL254
import GaussianSpectral254

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Matrix
open scoped ENNReal NNReal BigOperators Matrix
namespace Paper254

theorem klDiv_measurableEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (hint : Integrable (llr μ ν) μ) :
    klDiv (μ.map e) (ν.map e)=klDiv μ ν := by
  have hr := hac.ae_le (e.measurableEmbedding.rnDeriv_map μ ν)
  have he : (fun x => llr (μ.map e) (ν.map e) (e x)) =ᵐ[μ] llr μ ν := by
    filter_upwards [hr] with x hx
    simp only [llr,hx]
  have hi : Integrable (llr (μ.map e) (ν.map e)) (μ.map e) :=
    (integrable_map_equiv e _).mpr (hint.congr he.symm)
  have ha := e.measurableEmbedding.absolutelyContinuous_map hac
  rw [klDiv_of_ac_of_integrable ha hi,klDiv_of_ac_of_integrable hac hint,
    integral_map_equiv,integral_congr_ae he]
  simp [measureReal_def,Measure.map_apply e.measurable MeasurableSet.univ]

theorem mapped_gaussian_product_kl {d : ℕ} {β : Type*} [MeasurableSpace β]
    (e : (Fin d → ℝ) ≃ᵐ β) (u m : Fin d → ℝ) (q c : Fin d → ℝ≥0)
    (hq : ∀ i,q i ≠ 0) (hc : ∀ i,c i ≠ 0) :
    klDiv ((Measure.pi (fun i => gaussianReal (u i) (q i))).map e)
      ((Measure.pi (fun i => gaussianReal (m i) (c i))).map e)=
        ENNReal.ofReal (∑ i,coordinateKL (q i) (c i) (u i-m i)) := by
  have hformula := gaussian_product_kl_formula u m q c hq hc
  have hn : klDiv (Measure.pi (fun i => gaussianReal (u i) (q i)))
      (Measure.pi (fun i => gaussianReal (m i) (c i))) ≠ ∞ := by rw [hformula]; exact ENNReal.ofReal_ne_top
  have hh := klDiv_ne_top_iff.mp hn
  rw [klDiv_measurableEquiv e _ _ hh.1 hh.2,hformula]

def unitaryMeasurableEquiv {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ) :
    Coordinates d ≃ᵐ Coordinates d where
  toFun := fun x => (U : Precision d) *ᵥ x
  invFun := fun x => (star U : Matrix.unitaryGroup (Fin d) ℝ).val *ᵥ x
  left_inv := by
    intro x
    simp only [Matrix.mulVec_mulVec,unitary.coe_star,unitary.coe_star_mul_self,Matrix.one_mulVec]
  right_inv := by
    intro x
    simp only [Matrix.mulVec_mulVec,unitary.coe_mul_star_self,Matrix.one_mulVec]
  measurable_toFun := by
    change Measurable (fun x : Coordinates d => (U : Precision d) *ᵥ x)
    unfold Matrix.mulVec dotProduct
    fun_prop
  measurable_invFun := by
    change Measurable (fun x : Coordinates d => (star U : Matrix.unitaryGroup (Fin d) ℝ).val *ᵥ x)
    unfold Matrix.mulVec dotProduct
    fun_prop

def rotatedGaussian {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (m : Coordinates d) (c : Fin d → ℝ≥0) : Measure (Coordinates d) :=
  (Measure.pi (fun i => gaussianReal (((U : Precision d) *ᵥ m) i) (c i))).map
    (unitaryMeasurableEquiv U).symm

theorem rotatedGaussian_kl {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (u m : Coordinates d) (q c : Fin d → ℝ≥0)
    (hq : ∀ i,q i ≠ 0) (hc : ∀ i,c i ≠ 0) :
    klDiv (rotatedGaussian U u q) (rotatedGaussian U m c)=ENNReal.ofReal
      (∑ i,coordinateKL (q i) (c i) (((U : Precision d) *ᵥ (u-m)) i)) := by
  simpa only [rotatedGaussian,Matrix.mulVec_sub,Pi.sub_apply] using
    mapped_gaussian_product_kl (unitaryMeasurableEquiv U).symm
      ((U : Precision d) *ᵥ u) ((U : Precision d) *ᵥ m) q c hq hc

end Paper254
#print axioms Paper254.rotatedGaussian_kl
