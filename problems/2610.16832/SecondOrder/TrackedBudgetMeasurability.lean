import SecondOrder.TrackedBudgetRun

open MeasureTheory
open scoped Classical BigOperators

namespace SecondOrder
noncomputable section

theorem curvatureRequestPrice_measurable {A : Type*} [MeasurableSpace A] {d L : ℕ}
    (τ : ℝ) (κ : ℕ) {z : A → TrackedState d L} (hz : Measurable z) :
    Measurable (fun a => curvatureRequestPrice τ κ (z a)) :=
  Measurable.ite (trackedCurvatureNeeded_measurableSet τ hz) measurable_const measurable_const

/-- A measurable, sample-independent price for the entire post-move
block, even though the set of newly created nodes depends on history. -/
theorem postRequestPrice_measurable {A : Type*} [MeasurableSpace A] {d L : ℕ}
    (P : Parameters) (q : ℕ) (Lip s τ ρ δ : ℝ)
    {z : A → TrackedState d L} {r : A → CurvatureReply d} {b : A → Bool}
    (hz : Measurable z) (hr : Measurable r) (hb : Measurable b) :
    Measurable (fun a => postRequestPrice P q Lip s τ ρ δ (z a) (r a) (b a)) := by
  have hn := state_measurable_fields.mp (trackedNext_measurable Lip s τ hz hr hb)
  have hm := (tracked_measurable_fields.mp hz).2.2
  have hl := (trackerMemory_measurable_fields.mp hm).1
  have hp := trackerPushPoints_measurable hm hn.1
  have hs (n : ℕ) : Measurable (fun a => ∑ i ∈ createdNodes L n,
      localQueryCount (chordVariance P
        (trackerPushPoints (z a).memory (trackedNext Lip s τ (z a) (r a) (b a)).point (nodeLeft i))
        (trackerPushPoints (z a).memory (trackedNext Lip s τ (z a) (r a) (b a)).point (nodeRight i))) ρ δ) := by
    apply Finset.measurable_sum
    intro i hi
    exact adaptiveChordCost_measurable P (hp.eval (a := nodeLeft i)) (hp.eval (a := nodeRight i)) ρ δ
  have hsum := measurable_countable_lookup hs hl
  have hrun : MeasurableSet {a | (trackedNext Lip s τ (z a) (r a) (b a)).running = true} :=
    hn.2.1 (measurableSet_singleton true)
  simp only [postRequestPrice,requestOracleCost_decomposition,Nat.mul_zero,Nat.add_zero,
    trackedStepRequests_anchor]
  apply Measurable.add
  · exact (Measurable.ite (hrun.inter (trackedRestart_measurableSet q τ hz hr))
      measurable_const measurable_const).mul_const _
  · change Measurable (fun a => requestCharge
      (chordRequestCharge (fun x y => localQueryCount (chordVariance P x y) ρ δ))
      (trackedStepRequests q Lip s τ (z a) (r a) (b a)))
    simp only [trackedStepRequests_chordCharge]
    exact Measurable.ite hrun hsum measurable_const

variable {Ω Ψ A : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ] [MeasurableSpace A]
  {d L : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.budgetedTrackedStep_measurable (h : CommonLoss μ P ν F f)
    (q Q κ : ℕ) (Lip s τ ρ δ : ℝ) {routine : Point d → Ψ → CurvatureReply d}
    (hroutine : Measurable (fun w : Point d × Ψ => routine w.1 w.2))
    {z : A → QueryBudgetState (TrackedState d L)} {b : A → Bool}
    {tape : A → TrackingStepTape Ω Ψ P L τ δ}
    (hz : Measurable z) (hb : Measurable b) (hw : Measurable tape) :
    Measurable (fun a => budgetedTrackedStep P f q Q κ Lip s τ ρ δ routine (z a) (b a) (tape a)) := by
  have hc : Measurable (fun a => (z a).2.1+curvatureRequestPrice τ κ (z a).1) :=
    hz.snd.fst.add (curvatureRequestPrice_measurable τ κ hz.fst)
  have hr := sampledCurvature_measurable τ hroutine hz.fst hw.fst
  have hp : Measurable (fun a => (z a).2.1+curvatureRequestPrice τ κ (z a).1+
      postRequestPrice P q Lip s τ ρ δ (z a).1 (sampledCurvature τ routine (z a).1 (tape a).1) (b a)) :=
    hc.add (postRequestPrice_measurable P q Lip s τ ρ δ hz.fst hr hb)
  have hu := h.sampledPostStep_measurable q Lip s τ ρ δ hz.fst hr hb hw.snd
  exact Measurable.ite ((measurableSet_singleton true).preimage hz.snd.snd) hz
    (Measurable.ite (measurableSet_le hc measurable_const)
      (Measurable.ite (measurableSet_le hp measurable_const)
        (hu.prodMk (hp.prodMk measurable_const))
        (hz.fst.prodMk (hc.prodMk measurable_const)))
      (hz.fst.prodMk (hz.snd.fst.prodMk measurable_const)))

theorem CommonLoss.budgetedTrackedInitial_measurable (h : CommonLoss μ P ν F f)
    (Q : ℕ) (τ δ : ℝ) : Measurable (budgetedTrackedInitial (L := L) P f Q τ δ) := by
  unfold budgetedTrackedInitial
  split_ifs
  · exact (h.sampledInitial_measurable τ δ).prodMk measurable_const
  · exact measurable_const

/-- Joint measurability includes an arbitrary measurable sign path; the
independent finite fair-sign law can subsequently be substituted. -/
theorem CommonLoss.budgetedTrackedRun_measurable (h : CommonLoss μ P ν F f)
    (q Q κ : ℕ) (Lip s τ ρ δ : ℝ) {routine : Point d → Ψ → CurvatureReply d}
    (hm : Measurable (fun w : Point d × Ψ => routine w.1 w.2)) (N : ℕ)
    {anchor : A → LocalDraws Ω (P.gradientNoise^2) (τ/4) δ} {β : A → ℕ → Bool}
    {tape : A → Draws (TrackingStepTape Ω Ψ P L τ δ) N}
    (ha : Measurable anchor) (hb : Measurable β) (hw : Measurable tape) :
    Measurable (fun a => budgetedTrackedRun P f q Q κ Lip s τ ρ δ routine (anchor a) (β a) N (tape a)) := by
  induction N with
  | zero => exact (h.budgetedTrackedInitial_measurable Q τ δ).comp ha
  | succ N ih =>
    exact h.budgetedTrackedStep_measurable q Q κ Lip s τ ρ δ hm (ih hw.fst) (hb.eval (a := N)) hw.snd

end
end SecondOrder
