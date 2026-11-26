import SecondOrder.FreshTrackedRun

open MeasureTheory
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section

theorem sampledStepCallCount_measurable {A Ψ : Type*} [MeasurableSpace A] [MeasurableSpace Ψ]
    {d L : ℕ} (q : ℕ) (Lip s τ : ℝ) {routine : Point d → Ψ → CurvatureReply d}
    (hm : Measurable (fun w : Point d × Ψ => routine w.1 w.2))
    {z : A → TrackedState d L} {b : A → Bool} {tape : A → Ψ}
    (hz : Measurable z) (hb : Measurable b) (hw : Measurable tape) :
    Measurable (fun a => sampledStepCallCount q Lip s τ routine (z a) (b a) (tape a)) :=
  (Measurable.ite (trackedCurvatureNeeded_measurableSet τ hz) measurable_const measurable_const).add
    (postCallCount_measurable q Lip s τ hz (sampledCurvature_measurable τ hm hz hw) hb)

def freshTrackedCharge {Ω Ψ : Type*} {d L : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (q : ℕ) (Lip s τ ρ δ : ℝ) (routine : Point d → Ψ → CurvatureReply d) (g : Point d) (β : ℕ → Bool) :=
  fun N (w : Draws (TrackingStepTape Ω Ψ P L τ δ) N × TrackingStepTape Ω Ψ P L τ δ) =>
    (sampledStepCallCount q Lip s τ routine (freshTrackedRun P f q Lip s τ ρ δ routine g β N w.1) (β N) w.2.1 : ℝ≥0∞)*
      ENNReal.ofReal δ

theorem freshTrackedCharge_total {Ω Ψ : Type*} {d L : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (q : ℕ) (Lip s τ ρ δ : ℝ) (routine : Point d → Ψ → CurvatureReply d) (g : Point d) (β : ℕ → Bool)
    (N : ℕ) (w : Draws (TrackingStepTape Ω Ψ P L τ δ) N) :
    freshBatchCharge (freshTrackedCharge P f q Lip s τ ρ δ routine g β) N w =
      (freshTrackedCalls P f q Lip s τ ρ δ routine g β N w : ℝ≥0∞)*ENNReal.ofReal δ := by
  induction N with
  | zero => simp [freshBatchCharge,freshTrackedCalls]
  | succ N ih => simp only [freshBatchCharge,freshTrackedCharge,freshTrackedCalls,ih,Nat.cast_add,add_mul]

variable {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ] {d L : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.freshTrackedRun_measurable (h : CommonLoss μ P ν F f)
    (q : ℕ) (Lip s τ ρ δ : ℝ) {routine : Point d → Ψ → CurvatureReply d}
    (hm : Measurable (fun w : Point d × Ψ => routine w.1 w.2)) (β : ℕ → Bool) (N : ℕ) :
    Measurable (fun w : Point d × Draws (TrackingStepTape Ω Ψ P L τ δ) N =>
      freshTrackedRun P f q Lip s τ ρ δ routine w.1 β N w.2) := by
  simp only [freshTrackedRun_eq]
  exact (trackedRun_measurable q Lip s τ (h.finiteSampledSource_measurable q Lip s τ ρ δ hm N) N).comp
    (measurable_id.prodMk measurable_const)

/-- For every fixed sign path and every initial estimate, the actual
recursive fresh history fails with probability at most δ(4N+1). The
initial anchor failure is added separately, once. -/
theorem CommonLoss.freshTrackedFailure_bound (h : CommonLoss μ P ν F f)
    {η : Measure Ψ} [IsProbabilityMeasure η] {q : ℕ} (hq : 0 < q) (Lip s γ : ℝ)
    {τ ρ δ : ℝ} (hτ : 0 < τ) (hρ : 0 < ρ) (hδ : 0 < δ)
    {routine : Point d → Ψ → CurvatureReply d}
    (hm : Measurable (fun w : Point d × Ψ => routine w.1 w.2))
    (hc : ∀ x, η {w | ¬ValidCurvatureReply F γ x (routine x w)} ≤ ENNReal.ofReal δ)
    (g : Point d) (β : ℕ → Bool) (N : ℕ) :
    drawsLaw (trackingStepLaw μ η P L τ δ) N
      {w | ¬freshHistoryGood (freshTrackedFailure F P f q Lip s τ γ ρ δ routine g β) N w} ≤
        ENNReal.ofReal (((4*N+1 : ℕ) : ℝ)*δ) := by
  have hz (n : ℕ) : Measurable (freshTrackedRun (L := L) P f q Lip s τ ρ δ routine g β n) :=
    (h.freshTrackedRun_measurable q Lip s τ ρ δ hm β n).comp (measurable_const.prodMk measurable_id)
  apply fresh_batches_path_charge_bound
    (freshTrackedFailure F P f q Lip s τ γ ρ δ routine g β)
    (freshTrackedCharge P f q Lip s τ ρ δ routine g β)
  · intro n
    exact h.sampledStepFailure_measurableSet q Lip s τ γ ρ δ hm
      ((hz n).comp measurable_fst) measurable_const measurable_snd
  · intro n
    exact ((measurable_of_countable (fun k : ℕ => (k : ℝ≥0∞))).comp
      (sampledStepCallCount_measurable q Lip s τ hm ((hz n).comp measurable_fst) measurable_const measurable_snd.fst)).mul_const _
  · intro n w
    exact h.sampledStepFailure_confidence q Lip s γ hτ hρ hδ hm hc _ _
  · intro w
    rw [freshTrackedCharge_total,ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast]
    exact mul_le_mul_right' (by exact_mod_cast freshTrackedCalls_le P f hq Lip s τ ρ δ routine g β N w) _

end
end SecondOrder
