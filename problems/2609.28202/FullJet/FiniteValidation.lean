import FullJet.FiniteFailureBound

namespace FullJet

variable {α X : Type} [Fintype α] [Nonempty α]

theorem forall_snoc_iff (bad : α → Prop) {K : ℕ} (past : Fin K → α) (a : α) :
    (∀ i, bad (Fin.snoc (α := fun _ : Fin (K + 1) => α) past a i)) ↔
      (∀ i, bad (past i)) ∧ bad a := by
  constructor
  · intro h
    exact ⟨fun i => by simpa only [Fin.snoc_castSucc] using h i.castSucc,
      by simpa only [Fin.snoc_last] using h (Fin.last K)⟩
  · rintro ⟨hp, ha⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using ha
    · simpa only [Fin.snoc_castSucc] using hp j

theorem uniformMean_all_indicator (bad : α → Prop) [DecidablePred bad] (K : ℕ) :
    uniformMean (fun samples : Fin K → α => if ∀ i, bad (samples i) then (1 : ℝ) else 0) =
      uniformMean (fun a : α => if bad a then (1 : ℝ) else 0) ^ K := by
  classical
  induction K with
  | zero => simp
  | succ K ih =>
    rw [uniformMean_snoc]
    have hi (past : Fin K → α) (a : α) :
        (if ∀ i, bad (Fin.snoc (α := fun _ : Fin (K + 1) => α) past a i) then (1 : ℝ) else 0) =
          (if ∀ i, bad (past i) then (1 : ℝ) else 0) * (if bad a then 1 else 0) := by
      simp only [forall_snoc_iff]
      by_cases hp : ∀ i, bad (past i) <;> by_cases ha : bad a <;> simp [hp, ha]
    simp only [hi, uniformMean_mul]
    simp_rw [mul_comm _ (uniformMean (fun a : α => if bad a then (1 : ℝ) else 0))]
    rw [uniformMean_mul, ih, pow_succ, mul_comm]

theorem uniform_all_failure_probability (bad : α → Prop) (K : ℕ) :
    ((PMF.uniformOfFintype (Fin K → α)).toOuterMeasure {samples | ∀ i, bad (samples i)}).toReal =
      ((PMF.uniformOfFintype α).toOuterMeasure {a | bad a}).toReal ^ K := by
  classical
  simp only [pmf_event_eq_mean_indicator, Set.mem_setOf_eq]
  exact uniformMean_all_indicator bad K

/-- Retain a candidate only when exact validation accepts it. Later failed
attempts cannot overwrite a previously accepted point. -/
def validatedChoice (fallback : X) (accept : X → Prop) [DecidablePred accept] (candidate : α → X) :
    (K : ℕ) → (Fin K → α) → X
  | 0, _ => fallback
  | K + 1, samples =>
      if accept (candidate (samples (Fin.last K))) then candidate (samples (Fin.last K))
      else validatedChoice fallback accept candidate K (Fin.init samples)

theorem validatedChoice_failure_all (fallback : X) (accept : X → Prop) [DecidablePred accept]
    (candidate : α → X) (K : ℕ) (samples : Fin K → α)
    (h : ¬ accept (validatedChoice fallback accept candidate K samples)) :
    ∀ i, ¬ accept (candidate (samples i)) := by
  induction K with
  | zero => intro i; exact Fin.elim0 i
  | succ K ih =>
    have hlast : ¬ accept (candidate (samples (Fin.last K))) := by
      intro ha
      exact h (by simpa only [validatedChoice, if_pos ha] using ha)
    have hp : ¬ accept (validatedChoice fallback accept candidate K (Fin.init samples)) := by
      simpa only [validatedChoice, if_neg hlast] using h
    intro i
    refine Fin.lastCases hlast (fun j => ?_) i
    exact ih (Fin.init samples) hp j

theorem validatedChoice_failure_probability (fallback : X) (accept : X → Prop) [DecidablePred accept]
    (candidate : α → X) (K : ℕ) :
    ((PMF.uniformOfFintype (Fin K → α)).toOuterMeasure
      {samples | ¬ accept (validatedChoice fallback accept candidate K samples)}).toReal ≤
      ((PMF.uniformOfFintype α).toOuterMeasure {a | ¬ accept (candidate a)}).toReal ^ K := by
  classical
  rw [← uniform_all_failure_probability (fun a => ¬ accept (candidate a)) K]
  simp only [pmf_event_eq_mean_indicator, Set.mem_setOf_eq]
  apply pmfMean_mono
  intro samples
  by_cases hb : ¬ accept (validatedChoice fallback accept candidate K samples)
  · simp only [if_pos hb, if_pos (validatedChoice_failure_all fallback accept candidate K samples hb)]
    exact le_rfl
  · simp only [if_neg hb]
    split_ifs <;> norm_num

end FullJet
