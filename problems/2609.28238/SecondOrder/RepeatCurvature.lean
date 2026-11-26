import SecondOrder.CurvatureMeasurability
import SecondOrder.RobustBatch

open MeasureTheory
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section

/-- Retain the first negative reply; return a certificate only if every
independent trial returns its certificate branch. -/
def firstNegative {A : Type*} {d : ℕ} (r : A → CurvatureReply d) : (n : ℕ) → Draws A n → CurvatureReply d
  | 0, _ => .certificate
  | n+1, w => if curvatureTag (firstNegative r n w.1) = true then firstNegative r n w.1 else r w.2

def NegativeReplyBad {d : ℕ} (γ : ℝ) (H : Point d →L[ℝ] Point d) (r : CurvatureReply d) : Prop :=
  curvatureTag r = true ∧ ¬ RayleighReplyValid γ H r

theorem firstNegative_joint_measurable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    {d : ℕ} {r : X × A → CurvatureReply d} (hr : Measurable r) (n : ℕ) :
    Measurable (fun w : X × Draws A n => firstNegative (fun a => r (w.1,a)) n w.2) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hold := ih.comp (measurable_fst.prodMk (measurable_snd.fst :
      Measurable (fun w : X × (Draws A n × A) => w.2.1)))
    exact Measurable.ite ((curvatureTag_measurable.comp hold) (measurableSet_singleton true))
      hold (hr.comp (measurable_fst.prodMk measurable_snd.snd))

theorem firstNegative_measurable {A : Type*} [MeasurableSpace A] {d : ℕ}
    {r : A → CurvatureReply d} (hr : Measurable r) (n : ℕ) : Measurable (firstNegative r n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact Measurable.ite
      ((curvatureTag_measurable.comp (ih.comp measurable_fst)) (measurableSet_singleton true))
      (ih.comp measurable_fst) (hr.comp measurable_snd)

theorem firstNegative_bad_probability {A : Type*} [MeasurableSpace A] {d : ℕ}
    {μ : Measure A} [IsProbabilityMeasure μ] (r : A → CurvatureReply d)
    (γ : ℝ) (H : Point d →L[ℝ] Point d) {b : ℝ≥0∞}
    (hb : μ {a | NegativeReplyBad γ H (r a)} ≤ b) (n : ℕ) :
    drawsLaw μ n {w | NegativeReplyBad γ H (firstNegative r n w)} ≤ (n:ℝ≥0∞)*b := by
  induction n with
  | zero => simp [firstNegative, NegativeReplyBad, curvatureTag]
  | succ n ih =>
    have hs : {w : Draws A (n+1) | NegativeReplyBad γ H (firstNegative r (n+1) w)} ⊆
        ({w | NegativeReplyBad γ H (firstNegative r n w)} ×ˢ Set.univ) ∪
          (Set.univ ×ˢ {a | NegativeReplyBad γ H (r a)}) := by
      intro w hw
      change NegativeReplyBad γ H (firstNegative r (n+1) w) at hw
      by_cases ht : curvatureTag (firstNegative r n w.1) = true
      · exact Or.inl ⟨by simpa only [firstNegative, if_pos ht] using hw, Set.mem_univ _⟩
      · exact Or.inr ⟨Set.mem_univ _, by simpa only [firstNegative, if_neg ht] using hw⟩
    calc
      _ ≤ drawsLaw μ (n+1) (({w | NegativeReplyBad γ H (firstNegative r n w)} ×ˢ Set.univ) ∪
          (Set.univ ×ˢ {a | NegativeReplyBad γ H (r a)})) := measure_mono hs
      _ ≤ drawsLaw μ n {w | NegativeReplyBad γ H (firstNegative r n w)} +
          μ {a | NegativeReplyBad γ H (r a)} := by
        change ((drawsLaw μ n).prod μ) (_ ∪ _) ≤ _
        exact (measure_union_le _ _).trans_eq (by simp)
      _ ≤ (n:ℝ≥0∞)*b+b := add_le_add ih hb
      _ = ((n+1:ℕ):ℝ≥0∞)*b := by simp [Nat.cast_add, add_mul]

theorem firstNegative_certificate_probability {A : Type*} [MeasurableSpace A] {d : ℕ}
    {μ : Measure A} [IsProbabilityMeasure μ] (r : A → CurvatureReply d) (n : ℕ) :
    drawsLaw μ n {w | curvatureTag (firstNegative r n w) = false} =
      (μ {a | curvatureTag (r a) = false})^n := by
  induction n with
  | zero => simp [firstNegative, curvatureTag]
  | succ n ih =>
    have hs : {w : Draws A (n+1) | curvatureTag (firstNegative r (n+1) w) = false} =
        {w | curvatureTag (firstNegative r n w) = false} ×ˢ {a | curvatureTag (r a) = false} := by
      ext w
      change (curvatureTag (firstNegative r (n+1) w) = false) ↔
        (curvatureTag (firstNegative r n w.1) = false) ∧ (curvatureTag (r w.2) = false)
      cases ho : firstNegative r n w.1 <;> cases hn : r w.2 <;>
        simp [firstNegative, ho, hn, curvatureTag]
    rw [hs]
    change ((drawsLaw μ n).prod μ) (_ ×ˢ _) = _
    rw [Measure.prod_prod, ih, pow_succ]

/-- Wrong directions cost a union bound; an incorrect certificate costs
the probability that all independent trials miss a negative reply. -/
theorem firstNegative_failure_probability {A : Type*} [MeasurableSpace A] {d : ℕ}
    {μ : Measure A} [IsProbabilityMeasure μ] (r : A → CurvatureReply d)
    (γ : ℝ) (H : Point d →L[ℝ] Point d) {b q : ℝ≥0∞}
    (hb : μ {a | NegativeReplyBad γ H (r a)} ≤ b)
    (hq : ¬ RayleighCertificate γ H → μ {a | curvatureTag (r a) = false} ≤ q) (n : ℕ) :
    drawsLaw μ n {w | ¬ RayleighReplyValid γ H (firstNegative r n w)} ≤ (n:ℝ≥0∞)*b+q^n := by
  have hbn := firstNegative_bad_probability r γ H hb n
  by_cases hcert : RayleighCertificate γ H
  · have hs : {w | ¬ RayleighReplyValid γ H (firstNegative r n w)} ⊆
        {w | NegativeReplyBad γ H (firstNegative r n w)} := by
      intro w hw
      cases hr : firstNegative r n w <;> simp_all [NegativeReplyBad, curvatureTag, RayleighReplyValid]
    exact ((measure_mono hs).trans hbn).trans (le_add_right le_rfl)
  · have hs : {w | ¬ RayleighReplyValid γ H (firstNegative r n w)} ⊆
        {w | NegativeReplyBad γ H (firstNegative r n w)} ∪
          {w | curvatureTag (firstNegative r n w) = false} := by
      intro w hw
      cases hr : firstNegative r n w <;> simp_all [NegativeReplyBad, curvatureTag, RayleighReplyValid]
    refine (measure_mono hs).trans ((measure_union_le _ _).trans (add_le_add hbn ?_))
    rw [firstNegative_certificate_probability]
    exact pow_le_pow_left' (hq hcert) n

end
end SecondOrder
