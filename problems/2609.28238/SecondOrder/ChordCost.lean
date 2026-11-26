import SecondOrder.AdaptiveChord

open MeasureTheory

namespace SecondOrder
noncomputable section

variable {A : Type*} [MeasurableSpace A] {η : Measure A} [IsProbabilityMeasure η] {d : ℕ}

/-- The variable query count is integrable whenever squared chord length is.
Its expectation retains the quadratic energy term required by the tree bound. -/
theorem adaptiveChordCost_integral (P : Parameters) {x y : A → Point d}
    (hx : Measurable x) (hy : Measurable y) {ρ δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hE : Integrable (fun a => ‖y a-x a‖^2) η) :
    Integrable (fun a => (adaptiveChordCost P x y ρ δ a : ℝ)) η ∧
    (∫ a, (adaptiveChordCost P x y ρ δ a : ℝ) ∂η) ≤
      (36*(P.hessianNoise^2+P.gradientLip^2)*(∫ a, ‖y a-x a‖^2 ∂η)/ρ^2+2)*(8*Real.log (1/δ)+2) := by
  let C := 36*(P.hessianNoise^2+P.gradientLip^2)
  let D := 8*Real.log (1/δ)+2
  have henv : Integrable (fun a => (C*‖y a-x a‖^2/ρ^2+2)*D) η :=
    (((hE.const_mul C).div_const (ρ^2)).add (integrable_const 2)).mul_const D
  have hm : Measurable (fun a => (adaptiveChordCost P x y ρ δ a : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (adaptiveChordCost_measurable P hx hy ρ δ)
  have hi : Integrable (fun a => (adaptiveChordCost P x y ρ δ a : ℝ)) η := by
    apply henv.mono' hm.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro a
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact adaptiveChordCost_bound P x y hδ hδ1 a
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ a, (C*‖y a-x a‖^2/ρ^2+2)*D ∂η :=
      integral_mono hi henv (adaptiveChordCost_bound P x y hδ hδ1)
    _ = _ := by
      rw [integral_mul_const, integral_add ((hE.const_mul C).div_const (ρ^2)) (integrable_const 2),
        integral_div, integral_const_mul]
      simp [C, D]

theorem adaptiveChordCost_fresh_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Parameters) {x y : A → Point d}
    (hx : Measurable x) (hy : Measurable y) {ρ δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hE : Integrable (fun a => ‖y a-x a‖^2) η) :
    Integrable (fun w : A × BatchTape (ℝ × Ω) (confidenceRepeats δ) =>
      (adaptiveChordCost P x y ρ δ w.1 : ℝ)) (η.prod (batchTapeLaw (unitLine.prod μ) (confidenceRepeats δ))) ∧
    (∫ w : A × BatchTape (ℝ × Ω) (confidenceRepeats δ), (adaptiveChordCost P x y ρ δ w.1 : ℝ)
      ∂η.prod (batchTapeLaw (unitLine.prod μ) (confidenceRepeats δ))) ≤
        (36*(P.hessianNoise^2+P.gradientLip^2)*(∫ a, ‖y a-x a‖^2 ∂η)/ρ^2+2)*(8*Real.log (1/δ)+2) := by
  have hi := adaptiveChordCost_integral P hx hy (ρ := ρ) hδ hδ1 hE
  refine ⟨integrable_product_fst hi.1, ?_⟩
  rw [integral_fun_fst (fun a => (adaptiveChordCost P x y ρ δ a : ℝ))]
  simpa using hi.2

end
end SecondOrder
