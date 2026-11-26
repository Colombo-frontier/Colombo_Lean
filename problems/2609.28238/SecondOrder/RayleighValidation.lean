import SecondOrder.HessianRayleigh

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace SecondOrder
noncomputable section

def rayleighEstimate {Ω : Type*} {d : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (x v : Point d) (ρ δ : ℝ) : LocalDraws Ω (P.hessianBound^2) ρ δ → ℝ :=
  freshEstimate (hessianRayleigh f x v) (P.hessianBound^2) ρ δ

/-- The validator uses the supplied direction and entirely fresh samples. -/
def RayleighAccept {Ω : Type*} {d : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (x v : Point d) (γ δ : ℝ) (w : LocalDraws Ω (P.hessianBound^2) (γ/8) δ) : Prop :=
  ‖v‖ = 1 ∧ rayleighEstimate P f x v (γ/8) δ w ≤ -(5*γ/8)

theorem rayleighAccept_sound {Ω : Type*} {d : ℕ} (P : Parameters) (F : Point d → ℝ)
    (f : Ω → Point d → ℝ) (x v : Point d) (γ δ : ℝ)
    (w : LocalDraws Ω (P.hessianBound^2) (γ/8) δ)
    (ha : RayleighAccept P f x v γ δ w)
    (he : ‖rayleighEstimate P f x v (γ/8) δ w - ⟪hessian F x v,v⟫_ℝ‖ ≤ γ/8) :
    ‖v‖ = 1 ∧ ⟪hessian F x v,v⟫_ℝ ≤ -γ/2 := by
  have hb := (abs_le.mp (show |rayleighEstimate P f x v (γ/8) δ w -
    ⟪hessian F x v,v⟫_ℝ| ≤ γ/8 from he)).1
  exact ⟨ha.1, by have hh := ha.2; linarith⟩

theorem rayleighAccept_of_strong_negative {Ω : Type*} {d : ℕ} (P : Parameters)
    (F : Point d → ℝ) (f : Ω → Point d → ℝ) (x v : Point d) (γ δ : ℝ)
    (w : LocalDraws Ω (P.hessianBound^2) (γ/8) δ)
    (hv : ‖v‖ = 1) (hq : ⟪hessian F x v,v⟫_ℝ ≤ -(3*γ/4))
    (he : ‖rayleighEstimate P f x v (γ/8) δ w - ⟪hessian F x v,v⟫_ℝ‖ ≤ γ/8) :
    RayleighAccept P f x v γ δ w := by
  have hb := (abs_le.mp (show |rayleighEstimate P f x v (γ/8) δ w -
    ⟪hessian F x v,v⟫_ℝ| ≤ γ/8 from he)).2
  exact ⟨hv, by linarith⟩

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] {d : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {η : Measure A} [IsProbabilityMeasure η]
  {P : Parameters} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.rayleighEstimate_joint_measurable (h : CommonLoss μ P ν F f) (ρ δ : ℝ) :
    Measurable (fun w : (Point d × Point d) × LocalDraws Ω (P.hessianBound^2) ρ δ =>
      rayleighEstimate P f w.1.1 w.1.2 ρ δ w.2) :=
  freshEstimate_joint_measurable h.hessianRayleigh_measurable _ _ _

theorem CommonLoss.rayleighEstimate_confidence (h : CommonLoss μ P ν F f) (x v : Point d)
    (hv : ‖v‖ = 1) {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) :
    localLaw μ (P.hessianBound^2) ρ δ
      {w | ρ < ‖rayleighEstimate P f x v ρ δ w - ⟪hessian F x v,v⟫_ℝ‖} ≤ ENNReal.ofReal δ := by
  apply robustBatch_confidence
    (Measurable.comp
      (g := fun w : (Point d × Point d) × Ω => hessianRayleigh f w.1.1 w.1.2 w.2)
      (f := fun z : Ω => ((x,v),z)) h.hessianRayleigh_measurable
      (measurable_const.prodMk measurable_id))
    (h.hessianRayleigh_integrable x v) (h.hessianRayleigh_error_integrable x v)
    (h.hessianRayleigh_mean x v) _ hρ hδ
  simpa only [hv, one_pow, mul_one] using h.hessianRayleigh_bounded_variance x v

theorem CommonLoss.adaptiveRayleighEstimate_measurable (h : CommonLoss μ P ν F f)
    {x v : A → Point d} (hx : Measurable x) (hv : Measurable v) (ρ δ : ℝ) :
    Measurable (fun w : A × LocalDraws Ω (P.hessianBound^2) ρ δ =>
      rayleighEstimate P f (x w.1) (v w.1) ρ δ w.2) := by
  exact Measurable.comp
    (g := fun w : (Point d × Point d) × LocalDraws Ω (P.hessianBound^2) ρ δ =>
      rayleighEstimate P f w.1.1 w.1.2 ρ δ w.2)
    (f := fun w : A × LocalDraws Ω (P.hessianBound^2) ρ δ => ((x w.1,v w.1),w.2))
    (h.rayleighEstimate_joint_measurable ρ δ)
    (((hx.comp measurable_fst).prodMk (hv.comp measurable_fst)).prodMk measurable_snd)

theorem CommonLoss.adaptiveRayleighAccept_measurable (h : CommonLoss μ P ν F f)
    {x v : A → Point d} (hx : Measurable x) (hv : Measurable v) (γ δ : ℝ) :
    MeasurableSet {w : A × LocalDraws Ω (P.hessianBound^2) (γ/8) δ |
      RayleighAccept P f (x w.1) (v w.1) γ δ w.2} :=
  (measurableSet_eq_fun (hv.comp measurable_fst).norm measurable_const).inter
    (measurableSet_le (h.adaptiveRayleighEstimate_measurable hx hv (γ/8) δ) measurable_const)

/-- The unit-vector guard makes the bound valid for arbitrary measurable
histories, even histories on which candidate generation fails. -/
theorem CommonLoss.adaptiveRayleigh_past_confidence (h : CommonLoss μ P ν F f)
    {x v : A → Point d} (hx : Measurable x) (hv : Measurable v)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) {past : Set A} (hp : MeasurableSet past) :
    (η.prod (localLaw μ (P.hessianBound^2) ρ δ))
      {w | w.1 ∈ past ∧ ‖v w.1‖ = 1 ∧
        ρ < ‖rayleighEstimate P f (x w.1) (v w.1) ρ δ w.2 -
          ⟪hessian F (x w.1) (v w.1),v w.1⟫_ℝ‖} ≤ ENNReal.ofReal δ * η past := by
  have hq := h.populationRayleigh_measurable.comp
    ((hx.comp (measurable_fst : Measurable (Prod.fst :
      A × LocalDraws Ω (P.hessianBound^2) ρ δ → A))).prodMk (hv.comp measurable_fst))
  apply fresh_event_past_bound
    ((measurableSet_eq_fun (hv.comp measurable_fst).norm measurable_const).inter
      (measurableSet_lt measurable_const
        ((h.adaptiveRayleighEstimate_measurable hx hv ρ δ).sub hq).norm)) _ hp
  intro a
  change localLaw μ (P.hessianBound^2) ρ δ
    {w | ‖v a‖ = 1 ∧ ρ < ‖rayleighEstimate P f (x a) (v a) ρ δ w -
      ⟪hessian F (x a) (v a),v a⟫_ℝ‖} ≤ ENNReal.ofReal δ
  by_cases ha : ‖v a‖ = 1
  · simpa only [ha, true_and] using h.rayleighEstimate_confidence (x a) (v a) ha hρ hδ
  · simp only [ha, false_and, Set.setOf_false, measure_empty, zero_le]

theorem CommonLoss.adaptiveRayleigh_confidence (h : CommonLoss μ P ν F f)
    {x v : A → Point d} (hx : Measurable x) (hv : Measurable v)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) :
    (η.prod (localLaw μ (P.hessianBound^2) ρ δ))
      {w | ‖v w.1‖ = 1 ∧ ρ < ‖rayleighEstimate P f (x w.1) (v w.1) ρ δ w.2 -
        ⟪hessian F (x w.1) (v w.1),v w.1⟫_ℝ‖} ≤ ENNReal.ofReal δ := by
  simpa using h.adaptiveRayleigh_past_confidence (η := η) hx hv hρ hδ MeasurableSet.univ

end
end SecondOrder
