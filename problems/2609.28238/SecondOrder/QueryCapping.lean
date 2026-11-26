import SecondOrder.QueryProgram

open MeasureTheory Filter
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section

variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]

theorem callRun_measurable (initial : S) (update : ℕ → S → Ω → S)
    (hu : ∀ n, Measurable (fun w : S × Ω => update n w.1 w.2)) (n : ℕ) :
    Measurable (callRun initial update n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact (hu n).comp ((ih.comp measurable_fst).prodMk measurable_snd)

theorem callCost_measurable (initial : S) (request : ℕ → S → ℕ) (update : ℕ → S → Ω → S)
    (hc : ∀ n, Measurable (request n))
    (hu : ∀ n, Measurable (fun w : S × Ω => update n w.1 w.2)) (n : ℕ) :
    Measurable (callCost initial request update n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (ih.comp measurable_fst).add (((hc n).comp (callRun_measurable initial update hu n)).comp measurable_fst)

theorem queryBudgetStep_measurable (Q : ℕ) (request : S → ℕ) (update : S → Ω → S)
    (hc : Measurable request) (hu : Measurable (fun w : S × Ω => update w.1 w.2)) :
    Measurable (fun w : QueryBudgetState S × Ω => queryBudgetStep Q request update w.1 w.2) := by
  have hb : MeasurableSet {w : QueryBudgetState S × Ω | w.1.2.2 = true} :=
    (measurableSet_singleton true).preimage measurable_fst.snd.snd
  have hn : Measurable (fun w : QueryBudgetState S × Ω => w.1.2.1+request w.1.1) :=
    measurable_fst.snd.fst.add (hc.comp measurable_fst.fst)
  have hp : MeasurableSet {w : QueryBudgetState S × Ω | w.1.2.1+request w.1.1 ≤ Q} :=
    measurableSet_le hn measurable_const
  exact Measurable.ite hb measurable_fst (Measurable.ite hp
    ((hu.comp (measurable_fst.fst.prodMk measurable_snd)).prodMk (hn.prodMk measurable_const))
    (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk measurable_const)))

theorem queryBudgetRun_measurable (Q : ℕ) (initial : S) (request : ℕ → S → ℕ) (update : ℕ → S → Ω → S)
    (hc : ∀ n, Measurable (request n))
    (hu : ∀ n, Measurable (fun w : S × Ω => update n w.1 w.2)) (n : ℕ) :
    Measurable (queryBudgetRun Q initial request update n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (queryBudgetStep_measurable Q _ _ (hc n) (hu n)).comp
      ((ih.comp measurable_fst).prodMk measurable_snd)

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Markov's inequality applies to the cost of the coupled uncapped
program. The budgeted program itself never exceeds its deterministic cap. -/
theorem queryBudget_rejection_probability {Q : ℕ} (hQ : 0 < Q) (initial : S)
    (request : ℕ → S → ℕ) (update : ℕ → S → Ω → S) (n : ℕ)
    (hi : Integrable (fun w => (callCost initial request update n w : ℝ)) (drawsLaw μ n))
    {B : ℝ} (hB : (∫ w, (callCost initial request update n w : ℝ) ∂drawsLaw μ n) ≤ B) :
    drawsLaw μ n {w | (queryBudgetRun Q initial request update n w).2.2 = true} ≤
      ENNReal.ofReal (B/(Q : ℝ)) := by
  have hQr : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have hp := (hi.div_const (Q : ℝ)).measure_le_integral
    (Eventually.of_forall (fun w => by positivity))
    (s := {w | (queryBudgetRun Q initial request update n w).2.2 = true}) (fun w hw => by
      apply (le_div_iff₀ hQr).mpr
      simp only [one_mul]
      exact_mod_cast (queryBudgetRun_rejected_iff Q initial request update n w).mp hw |>.le)
  refine hp.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [integral_div]
  exact div_le_div_of_nonneg_right hB hQr.le

def queryCap (B : ℝ) : ℕ := ⌈24*(1+B)⌉₊

theorem queryCap_pos {B : ℝ} (hB : 0 ≤ B) : 0 < queryCap B := by
  have hc := Nat.le_ceil (24*(1+B))
  have hp : (0 : ℝ) < queryCap B := by dsimp [queryCap]; linarith
  exact Nat.cast_pos.mp hp

theorem queryCap_ratio {B : ℝ} (hB : 0 ≤ B) : B/(queryCap B : ℝ) ≤ 1/24 := by
  apply (div_le_iff₀ (Nat.cast_pos.mpr (queryCap_pos hB))).mpr
  have hc := Nat.le_ceil (24*(1+B))
  change 24*(1+B) ≤ (queryCap B : ℝ) at hc
  linarith

theorem queryBudget_rejection_twenty_fourth (initial : S) (request : ℕ → S → ℕ)
    (update : ℕ → S → Ω → S) (n : ℕ)
    (hi : Integrable (fun w => (callCost initial request update n w : ℝ)) (drawsLaw μ n))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : (∫ w, (callCost initial request update n w : ℝ) ∂drawsLaw μ n) ≤ B) :
    drawsLaw μ n {w | (queryBudgetRun (queryCap B) initial request update n w).2.2 = true} ≤
      ENNReal.ofReal (1/24 : ℝ) :=
  (queryBudget_rejection_probability (queryCap_pos hB0) initial request update n hi hB).trans
    (ENNReal.ofReal_le_ofReal (queryCap_ratio hB0))

/-- Adding a query cap increases failure probability by at most B/Q.
The output predicate can include termination, stationarity, or both. -/
theorem queryBudget_failure_bound {Q : ℕ} (hQ : 0 < Q) (initial : S)
    (request : ℕ → S → ℕ) (update : ℕ → S → Ω → S) (n : ℕ) (Good : S → Prop)
    (hi : Integrable (fun w => (callCost initial request update n w : ℝ)) (drawsLaw μ n))
    {B δ : ℝ} (hB0 : 0 ≤ B) (hδ : 0 ≤ δ)
    (hB : (∫ w, (callCost initial request update n w : ℝ) ∂drawsLaw μ n) ≤ B)
    (hf : drawsLaw μ n {w | ¬Good (callRun initial update n w)} ≤ ENNReal.ofReal δ) :
    drawsLaw μ n {w | (queryBudgetRun Q initial request update n w).2.2 = true ∨
      ¬Good (queryBudgetRun Q initial request update n w).1} ≤ ENNReal.ofReal (δ+B/(Q : ℝ)) := by
  have hs : {w | (queryBudgetRun Q initial request update n w).2.2 = true ∨
      ¬Good (queryBudgetRun Q initial request update n w).1} ⊆
      {w | ¬Good (callRun initial update n w)} ∪
      {w | (queryBudgetRun Q initial request update n w).2.2 = true} := by
    intro w hw
    change (queryBudgetRun Q initial request update n w).2.2 = true ∨
      ¬Good (queryBudgetRun Q initial request update n w).1 at hw
    by_cases hc : callCost initial request update n w ≤ Q
    · left
      rw [queryBudgetRun_agrees Q initial request update n w hc] at hw
      simpa using hw
    · right
      exact (queryBudgetRun_rejected_iff Q initial request update n w).mpr (Nat.lt_of_not_le hc)
  calc
    _ ≤ _ := measure_mono hs
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal δ+ENNReal.ofReal (B/(Q : ℝ)) :=
      add_le_add hf (queryBudget_rejection_probability hQ initial request update n hi hB)
    _ = _ := (ENNReal.ofReal_add hδ (div_nonneg hB0 (Nat.cast_nonneg Q))).symm

end
end SecondOrder
