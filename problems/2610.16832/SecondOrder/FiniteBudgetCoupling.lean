import SecondOrder.TrackedBudgetMeasurability

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

variable {Ω Ψ : Type*} {d L : ℕ}

/-- The actual finite sampler with an initial budget check and two
checks per later step, driven by independent finite tapes and signs. -/
def finiteBudgetedRun (P : Parameters) (f : Ω → Point d → ℝ) (q Q κ : ℕ) (Lip s τ ρ δ : ℝ)
    (routine : Point d → Ψ → CurvatureReply d) (M : ℕ)
    (w : FiniteTrackingTape Ω Ψ P L τ δ M × (Fin M → Bool)) : QueryBudgetState (TrackedState d L) :=
  budgetedTrackedRun P f q Q κ Lip s τ ρ δ routine w.1.1 (extendSigns w.2) M w.1.2

theorem freshTrackedRun_finite (P : Parameters) (f : Ω → Point d → ℝ) (q : ℕ) (Lip s τ ρ δ : ℝ)
    (routine : Point d → Ψ → CurvatureReply d) (M : ℕ)
    (w : FiniteTrackingTape Ω Ψ P L τ δ M × (Fin M → Bool)) :
    freshTrackedRun P f q Lip s τ ρ δ routine (gradientAnchor P f 0 (τ/4) δ w.1.1)
      (extendSigns w.2) M w.1.2 =
        trackedRun q Lip s τ (finiteActualSource P f q Lip s τ ρ δ routine M w.1) M w.2 := by
  rw [freshTrackedRun_eq]
  have he : (fun i : Fin M => extendSigns w.2 i.val) = w.2 := by
    funext i
    simp [extendSigns,i.isLt]
  rw [he]
  rfl

theorem freshTrackedPrice_finite (P : Parameters) (f : Ω → Point d → ℝ) (q κ : ℕ) (Lip s τ ρ δ : ℝ)
    (routine : Point d → Ψ → CurvatureReply d) (M : ℕ)
    (w : FiniteTrackingTape Ω Ψ P L τ δ M × (Fin M → Bool)) :
    freshTrackedPrice P f q κ Lip s τ ρ δ routine (gradientAnchor P f 0 (τ/4) δ w.1.1)
      (extendSigns w.2) M w.1.2 = requestCharge (requestOracleCost P τ ρ δ (fun _ => κ))
        (trackedRequestTrace q Lip s τ (finiteActualSource P f q Lip s τ ρ δ routine M w.1) M w.2) := by
  rw [freshTrackedPrice,freshTrackedRequests_eq,trackedRequestTrace_extendSigns]
  rfl

theorem finiteBudgetedRun_spent_le (P : Parameters) (f : Ω → Point d → ℝ) (q Q κ : ℕ) (Lip s τ ρ δ : ℝ)
    (routine : Point d → Ψ → CurvatureReply d) (M : ℕ)
    (w : FiniteTrackingTape Ω Ψ P L τ δ M × (Fin M → Bool)) :
    (finiteBudgetedRun P f q Q κ Lip s τ ρ δ routine M w).2.1 ≤ Q :=
  budgetedTrackedRun_spent_le P f q Q κ Lip s τ ρ δ routine w.1.1 (extendSigns w.2) M w.1.2

theorem finiteBudgetedRun_agrees (P : Parameters) (f : Ω → Point d → ℝ) (q Q κ : ℕ) (Lip s τ ρ δ : ℝ)
    (routine : Point d → Ψ → CurvatureReply d) (M : ℕ)
    (w : FiniteTrackingTape Ω Ψ P L τ δ M × (Fin M → Bool))
    (hc : requestCharge (requestOracleCost P τ ρ δ (fun _ => κ))
      (trackedRequestTrace q Lip s τ (finiteActualSource P f q Lip s τ ρ δ routine M w.1) M w.2) ≤ Q) :
    finiteBudgetedRun P f q Q κ Lip s τ ρ δ routine M w =
      (trackedRun q Lip s τ (finiteActualSource P f q Lip s τ ρ δ routine M w.1) M w.2,
        requestCharge (requestOracleCost P τ ρ δ (fun _ => κ))
          (trackedRequestTrace q Lip s τ (finiteActualSource P f q Lip s τ ρ δ routine M w.1) M w.2),false) := by
  rw [← freshTrackedPrice_finite P f q κ Lip s τ ρ δ routine M w] at hc
  rw [finiteBudgetedRun,budgetedTrackedRun_agrees P f q Q κ Lip s τ ρ δ routine _ _ _ _ hc,
    freshTrackedRun_finite,freshTrackedPrice_finite]

theorem finiteBudgetedRun_rejected_iff (P : Parameters) (f : Ω → Point d → ℝ) (q Q κ : ℕ) (Lip s τ ρ δ : ℝ)
    (routine : Point d → Ψ → CurvatureReply d) (M : ℕ)
    (w : FiniteTrackingTape Ω Ψ P L τ δ M × (Fin M → Bool)) :
    (finiteBudgetedRun P f q Q κ Lip s τ ρ δ routine M w).2.2 = true ↔
      Q < requestCharge (requestOracleCost P τ ρ δ (fun _ => κ))
        (trackedRequestTrace q Lip s τ (finiteActualSource P f q Lip s τ ρ δ routine M w.1) M w.2) := by
  rw [finiteBudgetedRun,budgetedTrackedRun_rejected_iff,freshTrackedPrice_finite]

def BudgetedFailure (F : Point d → ℝ) (ε γ : ℝ) (z : QueryBudgetState (TrackedState d L)) : Prop :=
  z.2.2 = true ∨ z.1.physical.running = true ∨ ¬IsSOSP F ε γ z.1.physical.point

/-- Exact event equivalence, including both kinds of budget rejection.
No accuracy assumption on the samples is used in this coupling. -/
theorem finiteBudgetedRun_failure_iff (P : Parameters) (f : Ω → Point d → ℝ) (F : Point d → ℝ)
    (q Q κ : ℕ) (Lip s τ ρ δ ε γ : ℝ) (routine : Point d → Ψ → CurvatureReply d) (M : ℕ)
    (w : FiniteTrackingTape Ω Ψ P L τ δ M × (Fin M → Bool)) :
    BudgetedFailure F ε γ (finiteBudgetedRun P f q Q κ Lip s τ ρ δ routine M w) ↔
      (trackedRun q Lip s τ (finiteActualSource P f q Lip s τ ρ δ routine M w.1) M w.2).physical.running = true ∨
      ¬IsSOSP F ε γ (trackedRun q Lip s τ (finiteActualSource P f q Lip s τ ρ δ routine M w.1) M w.2).physical.point ∨
      Q < requestCharge (requestOracleCost P τ ρ δ (fun _ => κ))
        (trackedRequestTrace q Lip s τ (finiteActualSource P f q Lip s τ ρ δ routine M w.1) M w.2) := by
  by_cases hc : requestCharge (requestOracleCost P τ ρ δ (fun _ => κ))
      (trackedRequestTrace q Lip s τ (finiteActualSource P f q Lip s τ ρ δ routine M w.1) M w.2) ≤ Q
  · simp only [BudgetedFailure,finiteBudgetedRun_agrees P f q Q κ Lip s τ ρ δ routine M w hc,
      Bool.false_eq_true,false_or,Nat.not_lt.mpr hc,or_false]
  · have hr := (finiteBudgetedRun_rejected_iff P f q Q κ Lip s τ ρ δ routine M w).mpr (Nat.lt_of_not_le hc)
    simp only [BudgetedFailure,hr,Nat.lt_of_not_le hc,true_or,or_true]

variable [MeasurableSpace Ω] [MeasurableSpace Ψ] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P : Parameters} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.finiteBudgetedRun_measurable (h : CommonLoss μ P ν F f)
    (q Q κ : ℕ) (Lip s τ ρ δ : ℝ) {routine : Point d → Ψ → CurvatureReply d}
    (hm : Measurable (fun w : Point d × Ψ => routine w.1 w.2)) (M : ℕ) :
    Measurable (finiteBudgetedRun (L := L) P f q Q κ Lip s τ ρ δ routine M) :=
  h.budgetedTrackedRun_measurable q Q κ Lip s τ ρ δ hm M measurable_fst.fst
    ((measurable_of_countable (fun b : Fin M → Bool => extendSigns b)).comp measurable_snd) measurable_fst.snd

theorem isSOSP_measurableSet {d : ℕ} {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) (ε γ : ℝ) :
    MeasurableSet {x | IsSOSP F ε γ x} :=
  (measurableSet_le (contDiff_gradient_one hF).continuous.measurable.norm measurable_const).inter
    ((rayleighCertificate_closed γ).measurableSet.preimage (continuous_hessian hF).measurable)

theorem budgetedFailure_measurableSet {A : Type*} [MeasurableSpace A] {d L : ℕ}
    {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) (ε γ : ℝ)
    {z : A → QueryBudgetState (TrackedState d L)} (hz : Measurable z) :
    MeasurableSet {a | BudgetedFailure F ε γ (z a)} := by
  have hp := state_measurable_fields.mp (tracked_measurable_fields.mp hz.fst).1
  exact ((measurableSet_singleton true).preimage hz.snd.snd).union
    ((hp.2.1 (measurableSet_singleton true)).union ((isSOSP_measurableSet hF ε γ).preimage hp.1).compl)

end
end SecondOrder
