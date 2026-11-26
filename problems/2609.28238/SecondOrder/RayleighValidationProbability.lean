import SecondOrder.RayleighValidation
import SecondOrder.OjaPopulationRayleigh

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace SecondOrder
noncomputable section

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] {d : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {η : Measure A} [IsProbabilityMeasure η]
  {P : Parameters} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

/-- Independent validation falsely accepts a direction with probability at
most δ, irrespective of the candidate generator and its history. -/
theorem CommonLoss.rayleigh_false_accept (h : CommonLoss μ P ν F f)
    {x v : A → Point d} (hx : Measurable x) (hv : Measurable v)
    {γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ) :
    (η.prod (localLaw μ (P.hessianBound^2) (γ/8) δ))
      {w | RayleighAccept P f (x w.1) (v w.1) γ δ w.2 ∧
        ¬ (‖v w.1‖ = 1 ∧ ⟪hessian F (x w.1) (v w.1),v w.1⟫_ℝ ≤ -γ/2)} ≤ ENNReal.ofReal δ := by
  refine (measure_mono ?_).trans (h.adaptiveRayleigh_confidence (η := η) hx hv (by positivity) hδ)
  intro w hw
  refine ⟨hw.1.1, ?_⟩
  by_contra hn
  exact hw.2 (rayleighAccept_sound P F f (x w.1) (v w.1) γ δ w.2 hw.1 (le_of_not_gt hn))

/-- A candidate success lower bound loses at most δ after validation. -/
theorem CommonLoss.rayleigh_accept_probability (h : CommonLoss μ P ν F f)
    {x v : A → Point d} (hx : Measurable x) (hv : Measurable v)
    {γ δ p : ℝ} (hγ : 0 < γ) (hδ : 0 < δ)
    (hp : p ≤ η.real {a | ‖v a‖ = 1 ∧ ⟪hessian F (x a) (v a),v a⟫_ℝ ≤ -(3*γ/4)}) :
    p-δ ≤ (η.prod (localLaw μ (P.hessianBound^2) (γ/8) δ)).real
      {w | RayleighAccept P f (x w.1) (v w.1) γ δ w.2} := by
  have he : p ≤ (η.prod (localLaw μ (P.hessianBound^2) (γ/8) δ)).real
      {w | ‖v w.1‖ = 1 ∧ ⟪hessian F (x w.1) (v w.1),v w.1⟫_ℝ ≤ -(3*γ/4)} := by
    have hs : {w : A × LocalDraws Ω (P.hessianBound^2) (γ/8) δ |
        ‖v w.1‖ = 1 ∧ ⟪hessian F (x w.1) (v w.1),v w.1⟫_ℝ ≤ -(3*γ/4)} =
        {a | ‖v a‖ = 1 ∧ ⟪hessian F (x a) (v a),v a⟫_ℝ ≤ -(3*γ/4)} ×ˢ Set.univ := by
      ext w; simp
    rw [hs, measureReal_prod_prod, measureReal_univ_eq_one, mul_one]
    exact hp
  have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (h.adaptiveRayleigh_confidence (η := η) hx hv (show 0 < γ/8 by positivity) hδ)
  rw [ENNReal.toReal_ofReal hδ.le] at hb
  apply probability_lower_outside_bad_event he hb
  intro w hw hn
  exact rayleighAccept_of_strong_negative P F f (x w.1) (v w.1) γ δ w.2 hw.1 hw.2
    (le_of_not_gt (fun he => hn ⟨hw.1,he⟩))

end
end SecondOrder
