import SecondOrder.ComparisonSuccessTransfer

open scoped BigOperators Classical ENNReal

universe u

namespace SecondOrder
noncomputable section
variable {H B : Type u} [Fintype H] [Fintype B]

/-- A slice of the actual joint law factors whenever both its event and its
history density are unchanged by replacing the hidden variable. -/
theorem finiteHiddenSlice_mean (μ : PMF H) (K : H → PMF B) (θ₀ : H)
    (E : H → B → Prop) (F : H → B → ℝ)
    (hE : ∀ θ h, E θ h ↔ E θ₀ h)
    (hK : ∀ θ h, E θ₀ h → K θ h=K θ₀ h) :
    pmfMean (finiteConditionalPMF μ K) (fun w => if E w.1 w.2 then F w.1 w.2 else 0)=
      pmfMean (K θ₀) (fun h => if E θ₀ h then pmfMean μ (fun θ => F θ h) else 0) := by
  rw [finiteConditionalPMF_mean]
  have he : ∀ θ, pmfMean (K θ) (fun h => if E θ h then F θ h else 0)=
      pmfMean (K θ₀) (fun h => if E θ₀ h then F θ h else 0) := by
    intro θ
    apply Finset.sum_congr rfl
    intro h _
    change (K θ h).toReal*(if E θ h then F θ h else 0)=
      (K θ₀ h).toReal*(if E θ₀ h then F θ h else 0)
    by_cases hh : E θ₀ h
    · rw [if_pos hh, if_pos ((hE θ h).mpr hh), hK θ h hh]
    · rw [if_neg hh, if_neg (fun hh' => hh ((hE θ h).mp hh'))]
      simp only [mul_zero]
  simp_rw [he]
  rw [pmfMean_comm]
  apply pmfMean_congr
  intro h
  by_cases hh : E θ₀ h
  · simp only [if_pos hh]
  · simp only [if_neg hh, pmfMean_const]

theorem finiteHiddenSlice_factor (μ : PMF H) (K : H → PMF B) (θ₀ : H)
    (E : H → B → Prop) (f : H → ℝ)
    (hE : ∀ θ h, E θ h ↔ E θ₀ h)
    (hK : ∀ θ h, E θ₀ h → K θ h=K θ₀ h) :
    pmfMean (finiteConditionalPMF μ K) (fun w => if E w.1 w.2 then f w.1 else 0)=
      pmfMean μ f * pmfEventProbability (K θ₀) (fun h => decide (E θ₀ h)) := by
  rw [finiteHiddenSlice_mean μ K θ₀ E (fun θ _ => f θ) hE hK, pmfEventProbability_mean, ←pmfMean_mul]
  apply pmfMean_congr
  intro h
  simp only [decide_eq_true_eq]
  split_ifs <;> simp

theorem finiteHiddenSlice_probability_le (μ : PMF H) (K : H → PMF B) (θ₀ : H)
    (E F : H → B → Prop)
    (hE : ∀ θ h, E θ h ↔ E θ₀ h)
    (hK : ∀ θ h, E θ₀ h → K θ h=K θ₀ h)
    {q : ℝ} (hF : ∀ h, E θ₀ h → pmfEventProbability μ (fun θ => decide (F θ h))≤q) :
    pmfEventProbability (finiteConditionalPMF μ K) (fun w => decide (E w.1 w.2 ∧ F w.1 w.2))≤
      q*pmfEventProbability (K θ₀) (fun h => decide (E θ₀ h)) := by
  rw [pmfEventProbability_mean]
  simp only [decide_eq_true_eq, ite_and]
  rw [finiteHiddenSlice_mean μ K θ₀ E (fun θ h => if F θ h then 1 else 0) hE hK,
    pmfEventProbability_mean, ←pmfMean_mul]
  apply pmfMean_mono
  intro h
  by_cases hh : E θ₀ h
  · simp only [if_pos hh, decide_eq_true_eq, mul_one]
    simpa only [pmfEventProbability_mean, decide_eq_true_eq] using hF h hh
  · simp only [if_neg hh, decide_eq_true_eq, mul_zero, le_refl]

end
end SecondOrder
