import SecondOrder.FiniteResponseEntropy
import SecondOrder.BinaryRelativeEntropy

open MeasureTheory InformationTheory
open scoped BigOperators Classical ENNReal

namespace SecondOrder
noncomputable section
variable {A : Type*} [Fintype A]

def pmfEventProbability (p : PMF A) (E : A → Bool) : ℝ := (p.map E true).toReal

theorem pmfEventProbability_mean (p : PMF A) (E : A → Bool) :
    pmfEventProbability p E = pmfMean p (fun a => if E a=true then 1 else 0) := by
  rw [←pmfMean_map p E (fun b => if b=true then 1 else 0)]
  simp [pmfMean, Fintype.sum_bool, pmfEventProbability]

theorem pmfEventProbability_nonneg (p : PMF A) (E : A → Bool) : 0≤pmfEventProbability p E :=
  ENNReal.toReal_nonneg

theorem pmfEventProbability_le_one (p : PMF A) (E : A → Bool) : pmfEventProbability p E≤1 := by
  rw [pmfEventProbability_mean]
  apply pmfMean_le_const
  intro a
  split_ifs <;> norm_num

theorem pmfEventProbability_const (p : PMF A) (b : Bool) :
    pmfEventProbability p (fun _ => b)=if b=true then 1 else 0 := by
  rw [pmfEventProbability_mean, pmfMean_const]

theorem pmfEventProbability_measure [MeasurableSpace A] [MeasurableSingletonClass A]
    (p : PMF A) (E : A → Bool) : p.toMeasure.real {a | E a=true}=pmfEventProbability p E := by
  have he : p.toMeasure {a | E a=true}=p.map E true := by
    change p.toMeasure (E ⁻¹' {true})=p.map E true
    rw [←PMF.toMeasure_map_apply E p {true} (measurable_of_countable _) (measurableSet_singleton _),
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  exact congrArg ENNReal.toReal he

theorem pmfKL_bool_lower (p q : PMF Bool) (hq : ∀ b, q b≠0) :
    (p true).toReal*Real.log (1/(q true).toReal)-Real.log 2≤pmfKL p q := by
  have hp := pmf_toReal_sum p
  have hqsum := pmf_toReal_sum q
  simp only [Fintype.sum_bool] at hp hqsum
  have hqt : 0<(q true).toReal := ENNReal.toReal_pos (hq true) (q.apply_ne_top true)
  have hqf : 0<(q false).toReal := ENNReal.toReal_pos (hq false) (q.apply_ne_top false)
  have hpt : (p true).toReal≤1 := by linarith [ENNReal.toReal_nonneg (a := p false)]
  have hqt1 : (q true).toReal<1 := by linarith only [hqsum, hqf]
  have hh := binary_entropy_lower (ENNReal.toReal_nonneg (a := p true)) hpt hqt hqt1
  have he : pmfKL p q=binaryKL (p true).toReal (q true).toReal := by
    simp only [pmfKL, Fintype.sum_bool]
    rw [weighted_log_div _ _ hqt.ne', weighted_log_div _ _ hqf.ne']
    have hpf : (p false).toReal=1-(p true).toReal := by linarith only [hp]
    have hqf' : (q false).toReal=1-(q true).toReal := by linarith only [hqsum]
    rw [hpf, hqf']
    unfold binaryKL
    ring
  rw [he]
  exact hh

/-- A rare reference event stays unlikely under a finite information budget.
The empty and full event cases are included explicitly. -/
theorem pmfEventProbability_information_bound (p q : PMF A)
    (hp : ∀ a, p a≠0) (hq : ∀ a, q a≠0) (E : A → Bool)
    {K B q₀ : ℝ} (hK : 0≤K) (hKL : pmfKL p q≤K)
    (hB : 0<B) (hq₀ : 0<q₀) (hq₁ : q₀<1)
    (hrare : pmfEventProbability q E≤q₀) (hlog : B≤Real.log (1/q₀)) :
    pmfEventProbability p E≤(K+Real.log 2)/B := by
  by_cases ht : ∃ a, E a=true
  · have hf : ∃ a, E a=false := by
      by_contra hn
      have he : E=(fun _ => true) := by
        funext a
        cases ha : E a
        · exact False.elim (hn ⟨a,ha⟩)
        · rfl
      rw [he, pmfEventProbability_const] at hrare
      norm_num at hrare
      linarith only [hrare, hq₁]
    have hsurj : Function.Surjective E := by
      intro b
      cases b
      · exact hf
      · exact ht
    have hqt : 0<pmfEventProbability q E :=
      ENNReal.toReal_pos (pmf_map_ne_zero q hq hsurj true) ((q.map E).apply_ne_top true)
    have hbin := pmfKL_bool_lower (p.map E) (q.map E) (pmf_map_ne_zero q hq hsurj)
    have hdata := pmfKL_map_le p q hp hq hsurj
    have hlog' : B≤Real.log (1/pmfEventProbability q E) :=
      hlog.trans (Real.log_le_log (by positivity) (one_div_le_one_div_of_le hqt hrare))
    have hmul := mul_le_mul_of_nonneg_left hlog' (pmfEventProbability_nonneg p E)
    apply (le_div_iff₀ hB).2
    change pmfEventProbability p E*Real.log (1/pmfEventProbability q E)-Real.log 2≤_ at hbin
    linarith only [hbin, hdata, hKL, hmul]
  · have he : E=(fun _ => false) := by
      funext a
      cases ha : E a
      · rfl
      · exact False.elim (ht ⟨a,ha⟩)
    rw [he, pmfEventProbability_const]
    norm_num only [Bool.false_eq_true, if_false]
    exact div_nonneg (add_nonneg hK (Real.log_nonneg (by norm_num))) hB.le

end
end SecondOrder
