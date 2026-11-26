import SecondOrder.OjaValidatedTrial
import SecondOrder.RepeatCurvature
import SecondOrder.OjaConfidenceScale

open MeasureTheory
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section

abbrev OjaAmplifiedDraws (Ω : Type*) (d : ℕ) (P : Parameters) (γ δ : ℝ) :=
  Draws (OjaTrialDraws Ω d P γ (ojaValidationFailure δ)) (ojaRepeats δ)

def ojaAmplifiedLaw {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (P : Parameters)
    {d : ℕ} (hd : 0 < d) {γ : ℝ} (hγ : 0 < γ) (δ : ℝ) : Measure (OjaAmplifiedDraws Ω d P γ δ) :=
  drawsLaw (ojaTrialLaw μ P hd hγ (ojaValidationFailure δ)) (ojaRepeats δ)

instance ojaAmplifiedLaw_probability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (P : Parameters) {d : ℕ} (hd : 0 < d) {γ : ℝ} (hγ : 0 < γ) (δ : ℝ) :
    IsProbabilityMeasure (ojaAmplifiedLaw μ P hd hγ δ) := by unfold ojaAmplifiedLaw; infer_instance

def ojaAmplifiedReply {Ω : Type*} {d : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (x : Point d) (γ δ : ℝ) : OjaAmplifiedDraws Ω d P γ δ → CurvatureReply d :=
  firstNegative (ojaTrialReply P f x γ (ojaValidationFailure δ)) (ojaRepeats δ)

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.ojaTrialReply_fixed_measurable (h : CommonLoss μ P ν F f)
    (x : Point d) (γ δ : ℝ) : Measurable (ojaTrialReply P f x γ δ) :=
  Measurable.comp
    (g := fun w : Point d × OjaTrialDraws Ω d P γ δ => ojaTrialReply P f w.1 γ δ w.2)
    (f := fun w : OjaTrialDraws Ω d P γ δ => (x,w))
    (h.ojaTrialReply_measurable γ δ) (measurable_const.prodMk measurable_id)

theorem CommonLoss.ojaTrial_miss_probability (h : CommonLoss μ P ν F f) (hd : 0 < d)
    {γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ) (hδsmall : δ ≤ 1/192) (x : Point d)
    (hbad : ¬ RayleighCertificate γ (hessian F x)) :
    ojaTrialLaw μ P hd hγ δ {w | curvatureTag (ojaTrialReply P f x γ δ w) = false} ≤
      ENNReal.ofReal (191/192:ℝ) := by
  have hp := h.ojaTrial_accept_probability hd hγ hδ x hbad
  have hm : MeasurableSet {w | curvatureTag (ojaTrialReply P f x γ δ w) = true} :=
    (curvatureTag_measurable.comp (h.ojaTrialReply_fixed_measurable x γ δ)) (measurableSet_singleton true)
  have he : {w | curvatureTag (ojaTrialReply P f x γ δ w) = false} =
      {w | curvatureTag (ojaTrialReply P f x γ δ w) = true}ᶜ := by
    ext w
    cases ht : curvatureTag (ojaTrialReply P f x γ δ w) <;> simp [ht]
  have hb : (ojaTrialLaw μ P hd hγ δ).real
      {w | curvatureTag (ojaTrialReply P f x γ δ w) = false} ≤ 191/192 := by
    rw [he, measureReal_compl hm, measureReal_univ_eq_one]
    linarith
  have hb' := ENNReal.ofReal_le_ofReal hb
  unfold Measure.real at hb'
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)] at hb'
  exact hb'

theorem CommonLoss.ojaAmplifiedReply_measurable (h : CommonLoss μ P ν F f) (γ δ : ℝ) :
    Measurable (fun w : Point d × OjaAmplifiedDraws Ω d P γ δ =>
      ojaAmplifiedReply P f w.1 γ δ w.2) :=
  firstNegative_joint_measurable (h.ojaTrialReply_measurable γ (ojaValidationFailure δ)) (ojaRepeats δ)

/-- A fully specified sampling algorithm, requiring no unknown population
quantity, returns a valid negative direction or a valid certificate with
failure probability at most δ. Here the ambient dimension is positive. -/
theorem CommonLoss.ojaAmplifiedReply_confidence (h : CommonLoss μ P ν F f) (hd : 0 < d)
    {γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (x : Point d) :
    ojaAmplifiedLaw μ P hd hγ δ
      {w | ¬ RayleighReplyValid γ (hessian F x) (ojaAmplifiedReply P f x γ δ w)} ≤ ENNReal.ofReal δ := by
  have hα := ojaValidationFailure_pos hδ
  have hb := firstNegative_failure_probability
    (μ := ojaTrialLaw μ P hd hγ (ojaValidationFailure δ))
    (ojaTrialReply P f x γ (ojaValidationFailure δ)) γ (hessian F x)
    (h.ojaTrial_false_negative_reply hd hγ hα x)
    (h.ojaTrial_miss_probability hd hγ hα (ojaValidationFailure_le hδ1) x) (ojaRepeats δ)
  refine hb.trans ?_
  have he : (ojaRepeats δ:ℝ≥0∞)*ENNReal.ofReal (ojaValidationFailure δ) = ENNReal.ofReal (δ/2) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ojaValidationFailure_total]
  rw [he, ← ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 191/192)]
  calc
    _ ≤ ENNReal.ofReal (δ/2) + ENNReal.ofReal (δ/2) :=
      add_le_add_left (ENNReal.ofReal_le_ofReal (ojaRepeats_sufficient hδ)) _
    _ = ENNReal.ofReal δ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

end
end SecondOrder
