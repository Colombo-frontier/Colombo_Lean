import NCConcave16991.FiniteProcess

/-! # Adaptive failure checks under genuine fresh independent finite seeds -/

open Set MeasureTheory

namespace NCConcave16991.FiniteProcess

noncomputable section

variable {I : Type*} [Finite I] [MeasurableSpace I] [MeasurableSingletonClass I]

/-- A check may use the entire preceding history, including all previous checks. -/
def everBad (bad : (t : ℕ) → History I t → I → Prop) :
    (t : ℕ) → History I t → Prop
  | 0, _ => False
  | t + 1, h => everBad bad t h.1 ∨ bad t h.1 h.2

def failureIndicator (bad : (t : ℕ) → History I t → I → Prop)
    (t : ℕ) (h : History I t) : ℝ := by
  classical
  exact if everBad bad t h then 1 else 0

theorem failureIndicator_integral (ν : Measure I) [IsProbabilityMeasure ν]
    (bad : (t : ℕ) → History I t → I → Prop) (t : ℕ) :
    (∫ h, failureIndicator bad t h ∂law ν t) = (law ν t).real {h | everBad bad t h} := by
  classical
  have he : failureIndicator bad t = ({h | everBad bad t h}).indicator (fun _ ↦ (1 : ℝ)) := by
    funext h
    simp [failureIndicator, Set.indicator]
  rw [he]
  exact integral_indicator_one ((Set.to_countable _).measurableSet)

/-- A uniform conditional failure probability gives a union bound for truly
adaptive checks. No independence of the check events is assumed. -/
theorem adaptive_failure_probability (ν : Measure I) [IsProbabilityMeasure ν]
    (bad : (t : ℕ) → History I t → I → Prop) {p : ℝ} (hp : 0 ≤ p)
    (hbad : ∀ t h, ν.real {i | bad t h i} ≤ p) (T : ℕ) :
    (law ν T).real {h | everBad bad T h} ≤ T * p := by
  classical
  have hlocal (t : ℕ) (h : History I t) :
      (∫ i, failureIndicator bad (t + 1) (h, i) ∂ν) ≤ failureIndicator bad t h + p := by
    by_cases hold : everBad bad t h
    · simp only [failureIndicator, everBad, hold, true_or, ↓reduceIte,
        integral_const, probReal_univ, one_smul]
      linarith
    · have he : (fun i ↦ failureIndicator bad (t + 1) (h, i)) =
          ({i | bad t h i}).indicator (fun _ ↦ (1 : ℝ)) := by
        funext i
        simp [failureIndicator, everBad, hold, Set.indicator]
      rw [he, integral_indicator_const (1 : ℝ) ((Set.to_countable _).measurableSet)]
      simpa only [smul_eq_mul, mul_one, failureIndicator, hold, ↓reduceIte, zero_add] using hbad t h
  have hexpect : ∀ t,
      (∫ h, failureIndicator bad t h ∂law ν t) ≤ t * p := by
    intro t
    induction t with
    | zero => simp [failureIndicator, everBad]
    | succ t ih =>
      have hh := integral_step_le ν t (failureIndicator bad (t + 1))
        (fun h ↦ failureIndicator bad t h + p) (hlocal t)
      letI : IsProbabilityMeasure (law ν t) := law_probability ν t
      rw [integral_add Integrable.of_finite Integrable.of_finite,
        integral_const, probReal_univ, one_smul] at hh
      push_cast
      linarith
  rw [← failureIndicator_integral ν bad T]
  exact hexpect T

end

end NCConcave16991.FiniteProcess
