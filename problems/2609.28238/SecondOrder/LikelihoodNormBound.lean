import Mathlib.InformationTheory.KullbackLeibler.Basic

open MeasureTheory InformationTheory
open scoped ENNReal

namespace SecondOrder
noncomputable section
variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Finite relative entropy controls the absolute first moment of the
log-likelihood ratio. The additive constant is used only for integrability. -/
theorem integral_norm_llr_le (hfin : klDiv μ ν ≠ ∞) :
    (∫ x, ‖llr μ ν x‖ ∂μ) ≤ (klDiv μ ν).toReal+2 := by
  obtain ⟨hac,hint⟩ := klDiv_ne_top_iff.mp hfin
  have hkl := (integrable_klFun_rnDeriv_iff hac).mpr hint
  have hr : Integrable (fun x => (μ.rnDeriv ν x).toReal) ν := Measure.integrable_toReal_rnDeriv
  have hm := (integrable_rnDeriv_mul_log_iff hac).mpr hint
  have hb (x : α) : ‖(μ.rnDeriv ν x).toReal*Real.log (μ.rnDeriv ν x).toReal‖ ≤
      klFun (μ.rnDeriv ν x).toReal+(μ.rnDeriv ν x).toReal+1 := by
    rw [Real.norm_eq_abs,abs_le]
    have hk := klFun_nonneg (ENNReal.toReal_nonneg (a := μ.rnDeriv ν x))
    have hn := ENNReal.toReal_nonneg (a := μ.rnDeriv ν x)
    simp only [klFun_apply] at hk ⊢
    constructor <;> linarith
  have he : (∫ x, ‖llr μ ν x‖ ∂μ) =
      ∫ x, ‖(μ.rnDeriv ν x).toReal*Real.log (μ.rnDeriv ν x).toReal‖ ∂ν := by
    rw [← integral_rnDeriv_smul hac]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [smul_eq_mul,llr_def,norm_mul,Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
  rw [he]
  calc
    _ ≤ ∫ x, klFun (μ.rnDeriv ν x).toReal+(μ.rnDeriv ν x).toReal+1 ∂ν :=
      integral_mono hm.norm ((hkl.add hr).add (integrable_const _)) hb
    _ = (klDiv μ ν).toReal+2 := by
      rw [integral_add (f := fun x => klFun (μ.rnDeriv ν x).toReal+(μ.rnDeriv ν x).toReal)
          (g := fun _ => (1:ℝ)) (hkl.add hr) (integrable_const _),integral_add hkl hr,
        ← toReal_klDiv_eq_integral_klFun hac,Measure.integral_toReal_rnDeriv hac,integral_const]
      simp only [measureReal_def,measure_univ,ENNReal.toReal_one,smul_eq_mul,one_mul]
      ring

end
end SecondOrder
