import SecondOrder.OjaNegativeCandidate
import SecondOrder.RayleighValidationProbability
import SecondOrder.RayleighValidationCost
import SecondOrder.CurvatureMeasurability

open MeasureTheory
open scoped InnerProductSpace Classical ENNReal

namespace SecondOrder
noncomputable section

abbrev OjaCandidateDraws (Ω : Type*) (d : ℕ) (P : Parameters) (γ : ℝ) :=
  (Draws Ω (ojaIterationCount d (ojaCurvatureTolerance P γ)) × (Fin d → Bool)) ×
    Fin (ojaIterationCount d (ojaCurvatureTolerance P γ))

abbrev OjaTrialDraws (Ω : Type*) (d : ℕ) (P : Parameters) (γ δ : ℝ) :=
  OjaCandidateDraws Ω d P γ × LocalDraws Ω (P.hessianBound^2) (γ/8) δ

def ojaTrialLaw {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (P : Parameters)
    {d : ℕ} (hd : 0 < d) {γ : ℝ} (hγ : 0 < γ) (δ : ℝ) : Measure (OjaTrialDraws Ω d P γ δ) :=
  (ojaCandidateLaw μ d (ojaIterationCount d (ojaCurvatureTolerance P γ))
    (ojaIterationCount_pos hd (ojaCurvatureTolerance_pos P hγ))).prod
      (localLaw μ (P.hessianBound^2) (γ/8) δ)

instance ojaTrialLaw_probability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (P : Parameters) {d : ℕ} (hd : 0 < d) {γ : ℝ} (hγ : 0 < γ) (δ : ℝ) :
    IsProbabilityMeasure (ojaTrialLaw μ P hd hγ δ) := by unfold ojaTrialLaw; infer_instance

def ojaTrialCandidate {Ω : Type*} {d : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (x : Point d) (γ : ℝ) : OjaCandidateDraws Ω d P γ → Point d :=
  ojaCandidate P f (ojaLearningRate d (ojaCurvatureTolerance P γ)) x
    (ojaIterationCount d (ojaCurvatureTolerance P γ))

/-- A single candidate plus independent validation. Its certificate branch
is only a failed trial; repetition is needed for a reliable certificate. -/
def rayleighValidatedReply {Ω : Type*} {d : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (x v : Point d) (γ δ : ℝ) (w : LocalDraws Ω (P.hessianBound^2) (γ/8) δ) : CurvatureReply d :=
  if RayleighAccept P f x v γ δ w then .negative v else .certificate

def ojaTrialReply {Ω : Type*} {d : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (x : Point d) (γ δ : ℝ) (w : OjaTrialDraws Ω d P γ δ) : CurvatureReply d :=
  rayleighValidatedReply P f x (ojaTrialCandidate P f x γ w.1) γ δ w.2

theorem ojaTrialReply_tag {Ω : Type*} {d : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (x : Point d) (γ δ : ℝ) (w : OjaTrialDraws Ω d P γ δ) :
    curvatureTag (ojaTrialReply P f x γ δ w) = true ↔
      RayleighAccept P f x (ojaTrialCandidate P f x γ w.1) γ δ w.2 := by
  unfold ojaTrialReply rayleighValidatedReply
  split <;> simp_all [curvatureTag]

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.ojaTrialCandidate_measurable (h : CommonLoss μ P ν F f) (γ : ℝ) :
    Measurable (fun w : Point d × OjaCandidateDraws Ω d P γ => ojaTrialCandidate P f w.1 γ w.2) :=
  h.ojaCandidate_measurable _ _

theorem CommonLoss.ojaTrialCandidate_fixed_measurable (h : CommonLoss μ P ν F f)
    (x : Point d) (γ : ℝ) : Measurable (ojaTrialCandidate P f x γ) :=
  Measurable.comp
    (g := fun w : Point d × OjaCandidateDraws Ω d P γ => ojaTrialCandidate P f w.1 γ w.2)
    (f := fun w : OjaCandidateDraws Ω d P γ => (x,w))
    (h.ojaTrialCandidate_measurable γ) (measurable_const.prodMk measurable_id)

theorem CommonLoss.rayleighValidatedReply_measurable (h : CommonLoss μ P ν F f) (γ δ : ℝ) :
    Measurable (fun w : (Point d × Point d) × LocalDraws Ω (P.hessianBound^2) (γ/8) δ =>
      rayleighValidatedReply P f w.1.1 w.1.2 γ δ w.2) := by
  unfold rayleighValidatedReply
  exact Measurable.ite (h.adaptiveRayleighAccept_measurable measurable_fst measurable_snd γ δ)
    (curvatureNegative_measurable.comp measurable_fst.snd) measurable_const

theorem CommonLoss.ojaTrialReply_measurable (h : CommonLoss μ P ν F f) (γ δ : ℝ) :
    Measurable (fun w : Point d × OjaTrialDraws Ω d P γ δ => ojaTrialReply P f w.1 γ δ w.2) := by
  have hv : Measurable (fun w : Point d × OjaTrialDraws Ω d P γ δ =>
      ojaTrialCandidate P f w.1 γ w.2.1) :=
    Measurable.comp
      (g := fun w : Point d × OjaCandidateDraws Ω d P γ => ojaTrialCandidate P f w.1 γ w.2)
      (f := fun w : Point d × OjaTrialDraws Ω d P γ δ => (w.1,w.2.1))
      (h.ojaTrialCandidate_measurable γ) (measurable_fst.prodMk measurable_snd.fst)
  exact Measurable.comp
    (g := fun w : (Point d × Point d) × LocalDraws Ω (P.hessianBound^2) (γ/8) δ =>
      rayleighValidatedReply P f w.1.1 w.1.2 γ δ w.2)
    (f := fun w : Point d × OjaTrialDraws Ω d P γ δ =>
      ((w.1,ojaTrialCandidate P f w.1 γ w.2.1),w.2.2))
    (h.rayleighValidatedReply_measurable γ δ)
    ((measurable_fst.prodMk hv).prodMk measurable_snd.snd)

theorem CommonLoss.ojaTrial_accept_probability (h : CommonLoss μ P ν F f) (hd : 0 < d)
    {γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ) (x : Point d)
    (hbad : ¬ RayleighCertificate γ (hessian F x)) :
    (1:ℝ)/96-δ ≤ (ojaTrialLaw μ P hd hγ δ).real
      {w | curvatureTag (ojaTrialReply P f x γ δ w) = true} := by
  simp only [ojaTrialReply_tag]
  exact h.rayleigh_accept_probability measurable_const (h.ojaTrialCandidate_fixed_measurable x γ)
    hγ hδ (h.oja_negative_candidate hd hγ x hbad)

theorem CommonLoss.ojaTrial_false_negative_reply (h : CommonLoss μ P ν F f) (hd : 0 < d)
    {γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ) (x : Point d) :
    ojaTrialLaw μ P hd hγ δ
      {w | curvatureTag (ojaTrialReply P f x γ δ w) = true ∧
        ¬ RayleighReplyValid γ (hessian F x) (ojaTrialReply P f x γ δ w)} ≤ ENNReal.ofReal δ := by
  have hb := h.rayleigh_false_accept
    (x := fun _ : OjaCandidateDraws Ω d P γ => x)
    (η := ojaCandidateLaw μ d (ojaIterationCount d (ojaCurvatureTolerance P γ))
      (ojaIterationCount_pos hd (ojaCurvatureTolerance_pos P hγ)))
    measurable_const (h.ojaTrialCandidate_fixed_measurable x γ) hγ hδ
  refine (measure_mono ?_).trans hb
  intro w hw
  have ha := (ojaTrialReply_tag P f x γ δ w).mp hw.1
  refine ⟨ha, ?_⟩
  simpa only [ojaTrialReply, rayleighValidatedReply, if_pos ha, RayleighReplyValid] using hw.2

end
end SecondOrder
