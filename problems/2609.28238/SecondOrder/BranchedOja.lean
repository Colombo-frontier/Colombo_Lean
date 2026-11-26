import SecondOrder.OjaTolerancePrice

open MeasureTheory
open scoped Classical ENNReal InnerProductSpace

namespace SecondOrder
noncomputable section

theorem measurable_prod_sum_elim {X A B E : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace E] {l : X × A → E} {r : X × B → E}
    (hl : Measurable l) (hr : Measurable r) :
    Measurable (fun w : X × (A ⊕ B) => w.2.elim (fun a => l (w.1,a)) (fun b => r (w.1,b))) := by
  have hs : Measurable (fun w : (X × A) ⊕ (X × B) => w.elim l r) := measurable_sum hl hr
  have hm := hs.comp (MeasurableEquiv.prodSumDistrib X A B).measurable
  convert hm using 1
  funext w
  rcases w with ⟨x,a|b⟩ <;> rfl

/-- Both branches can be recognized without observing any oracle reply. -/
def zeroQueryCurvatureCase (P : Parameters) (d : ℕ) (γ : ℝ) : Prop :=
  d = 0 ∨ P.gradientLip ≤ γ

theorem not_zeroQueryCurvatureCase_dimension {P : Parameters} {d : ℕ} {γ : ℝ}
    (hc : ¬ zeroQueryCurvatureCase P d γ) : 0 < d := by
  unfold zeroQueryCurvatureCase at hc
  omega

theorem not_zeroQueryCurvatureCase_tolerance {P : Parameters} {d : ℕ} {γ : ℝ}
    (hc : ¬ zeroQueryCurvatureCase P d γ) : γ ≤ 4*eigenHessianBound P := by
  have hl : γ < P.gradientLip := lt_of_not_ge (fun hh => hc (Or.inr hh))
  have hL := P.gradientLip_pos
  have hB := P.hessianBound_pos
  unfold eigenHessianBound
  linarith

abbrev BranchedOjaDraws (Ω : Type*) (d : ℕ) (P : Parameters) (γ δ : ℝ) :=
  PUnit ⊕ OjaAmplifiedDraws Ω d P γ δ

def branchedOjaLaw {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (P : Parameters)
    (d : ℕ) {γ : ℝ} (hγ : 0 < γ) (δ : ℝ) : Measure (BranchedOjaDraws Ω d P γ δ) :=
  if hc : zeroQueryCurvatureCase P d γ then Measure.dirac (Sum.inl PUnit.unit) else
    Measure.map Sum.inr (ojaAmplifiedLaw μ P (not_zeroQueryCurvatureCase_dimension hc) hγ δ)

instance branchedOjaLaw_probability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (P : Parameters) (d : ℕ) {γ : ℝ} (hγ : 0 < γ) (δ : ℝ) :
    IsProbabilityMeasure (branchedOjaLaw μ P d hγ δ) := by
  unfold branchedOjaLaw
  split
  · infer_instance
  · exact isProbabilityMeasure_map measurable_inr.aemeasurable

def branchedOjaReply {Ω : Type*} {d : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (x : Point d) (γ δ : ℝ) (w : BranchedOjaDraws Ω d P γ δ) : CurvatureReply d :=
  if zeroQueryCurvatureCase P d γ then .certificate else
    w.elim (fun _ => .certificate) (ojaAmplifiedReply P f x γ δ)

def branchedOjaQueryCount (P : Parameters) (d : ℕ) (γ δ : ℝ) : ℕ :=
  if zeroQueryCurvatureCase P d γ then 0 else ojaAmplifiedQueryCount P d γ δ

def branchedOjaTrace {Ω : Type*} {d : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (x : Point d) (γ δ : ℝ) (w : BranchedOjaDraws Ω d P γ δ) : List (Ω × HvpQuery d) :=
  if zeroQueryCurvatureCase P d γ then [] else
    w.elim (fun _ => []) (ojaAmplifiedTrace P f x γ δ)

theorem branchedOjaTrace_length_le {Ω : Type*} {d : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (x : Point d) (γ δ : ℝ) (w : BranchedOjaDraws Ω d P γ δ) :
    (branchedOjaTrace P f x γ δ w).length ≤ branchedOjaQueryCount P d γ δ := by
  by_cases hc : zeroQueryCurvatureCase P d γ
  · simp [branchedOjaTrace, branchedOjaQueryCount, hc]
  · cases w <;> simp [branchedOjaTrace, branchedOjaQueryCount, hc, ojaAmplifiedTrace_length]

theorem branchedOjaQueryCount_rate (P : Parameters) (d : ℕ)
    {ν ε γ : ℝ} (hν : 0 < ν) (hε : 0 < ε) (hε1 : ε ≤ 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    (branchedOjaQueryCount P d γ (localFailureTolerance (physicalCap P ν (ε/10) γ)):ℝ) ≤
      ojaSelectedPriceCoefficient P ν d*(toleranceLog ε γ)^4/γ^2 := by
  by_cases hc : zeroQueryCurvatureCase P d γ
  · simp only [branchedOjaQueryCount, if_pos hc, Nat.cast_zero]
    have hC := ojaSelectedPriceCoefficient_pos P hν d
    positivity
  · simpa only [branchedOjaQueryCount, if_neg hc] using
      ojaSelectedQueryCount_rate P (not_zeroQueryCurvatureCase_dimension hc) hν hε hε1 hγ hγ1
        (not_zeroQueryCurvatureCase_tolerance hc)

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.zeroQueryCurvatureCertificate (h : CommonLoss μ P ν F f)
    {γ : ℝ} (hc : zeroQueryCurvatureCase P d γ) (x : Point d) : RayleighCertificate γ (hessian F x) := by
  rcases hc with hd | hγ
  · subst d
    intro v
    have hv : v = 0 := Subsingleton.elim _ _
    simp [hv]
  · intro v
    have hb := (abs_le.mp (rayleigh_abs_le_of_norm_le (h.population_hessian_norm x) v)).1
    have hm := mul_le_mul_of_nonneg_right hγ (sq_nonneg ‖v‖)
    nlinarith

theorem CommonLoss.branchedOjaReply_measurable (h : CommonLoss μ P ν F f) (γ δ : ℝ) :
    Measurable (fun w : Point d × BranchedOjaDraws Ω d P γ δ => branchedOjaReply P f w.1 γ δ w.2) := by
  by_cases hc : zeroQueryCurvatureCase P d γ
  · simpa only [branchedOjaReply, if_pos hc] using
      (measurable_const : Measurable (fun _ : Point d × BranchedOjaDraws Ω d P γ δ =>
        (CurvatureReply.certificate : CurvatureReply d)))
  · simp only [branchedOjaReply, if_neg hc]
    exact measurable_prod_sum_elim
      (l := fun _ : Point d × PUnit => (CurvatureReply.certificate : CurvatureReply d))
      (r := fun w : Point d × OjaAmplifiedDraws Ω d P γ δ => ojaAmplifiedReply P f w.1 γ δ w.2)
      measurable_const (h.ojaAmplifiedReply_measurable γ δ)

theorem CommonLoss.branchedOjaReply_fixed_measurable (h : CommonLoss μ P ν F f)
    (x : Point d) (γ δ : ℝ) : Measurable (branchedOjaReply P f x γ δ) :=
  Measurable.comp
    (g := fun w : Point d × BranchedOjaDraws Ω d P γ δ => branchedOjaReply P f w.1 γ δ w.2)
    (f := fun w : BranchedOjaDraws Ω d P γ δ => (x,w))
    (h.branchedOjaReply_measurable γ δ) (measurable_const.prodMk measurable_id)

/-- Uniform in the dimension, with a genuinely zero-query branch for
zero dimension or a tolerance already implied by gradient smoothness. -/
theorem CommonLoss.branchedOjaReply_confidence (h : CommonLoss μ P ν F f)
    {γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (x : Point d) :
    branchedOjaLaw μ P d hγ δ
      {w | ¬ RayleighReplyValid γ (hessian F x) (branchedOjaReply P f x γ δ w)} ≤ ENNReal.ofReal δ := by
  by_cases hc : zeroQueryCurvatureCase P d γ
  · have hcert := h.zeroQueryCurvatureCertificate hc x
    simp [branchedOjaReply, hc, RayleighReplyValid, hcert]
  · have hm : MeasurableSet {w : BranchedOjaDraws Ω d P γ δ |
        ¬ RayleighReplyValid γ (hessian F x) (branchedOjaReply P f x γ δ w)} :=
      (rayleighReplyValid_measurableSet γ
      (measurable_const : Measurable (fun _ : BranchedOjaDraws Ω d P γ δ => hessian F x))
      (h.branchedOjaReply_fixed_measurable x γ δ)).compl
    rw [branchedOjaLaw, dif_neg hc, Measure.map_apply measurable_inr hm]
    simpa only [Set.preimage_setOf_eq, branchedOjaReply, if_neg hc, Sum.elim_inr] using
      h.ojaAmplifiedReply_confidence (not_zeroQueryCurvatureCase_dimension hc) hγ hδ hδ1 x

end
end SecondOrder
