import SecondOrder.SampledTrackingSource
import SecondOrder.FreshBatchUnion

open MeasureTheory
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section

def sampledStepFailure {Ω Ψ : Type*} {d L : ℕ} (F : Point d → ℝ) (P : Parameters)
    (f : Ω → Point d → ℝ) (q : ℕ) (Lip s τ γ ρ δ : ℝ)
    (routine : Point d → Ψ → CurvatureReply d) (z : TrackedState d L) (b : Bool)
    (w : TrackingStepTape Ω Ψ P L τ δ) : Prop :=
  (trackedCurvatureNeeded τ z ∧ ¬ValidCurvatureReply F γ z.physical.point (sampledCurvature τ routine z w.1)) ∨
    sampledPostFailure F P f q Lip s τ ρ δ z (sampledCurvature τ routine z w.1) b w.2

def sampledStepCallCount {Ψ : Type*} {d L : ℕ} (q : ℕ) (Lip s τ : ℝ)
    (routine : Point d → Ψ → CurvatureReply d) (z : TrackedState d L) (b : Bool) (w : Ψ) : ℕ :=
  (if trackedCurvatureNeeded τ z then 1 else 0)+postCallCount q Lip s τ z (sampledCurvature τ routine z w) b

theorem sampledStepCallCount_eq_requests {Ψ : Type*} {d L : ℕ} (q : ℕ) (Lip s τ : ℝ)
    (routine : Point d → Ψ → CurvatureReply d) (z : TrackedState d L) (b : Bool) (w : Ψ) :
    sampledStepCallCount q Lip s τ routine z b w =
      (trackedStepRequests q Lip s τ z (sampledCurvature τ routine z w) b).length := by
  rw [requestCharge_length,trackedStepRequests_curvature]
  have hp := postCallCount_eq_requests q Lip s τ z (sampledCurvature τ routine z w) b
  unfold sampledStepCallCount
  omega

/-- This failure event is exactly the failure of the invariant required
by the existing tracking execution; it introduces no stronger event. -/
theorem sampledStepFailure_iff {Ω Ψ : Type*} {d L : ℕ} (F : Point d → ℝ) (P : Parameters)
    (f : Ω → Point d → ℝ) (q : ℕ) (Lip s τ γ ρ δ : ℝ)
    (routine : Point d → Ψ → CurvatureReply d) (z : TrackedState d L) (b : Bool)
    (w : TrackingStepTape Ω Ψ P L τ δ) :
    ¬sampledStepFailure F P f q Lip s τ γ ρ δ routine z b w ↔
      TrackedLocalGood F q Lip s τ γ ρ z (sampledCurvature τ routine z w.1) b
        (sampledChordPacket P f Lip s τ ρ δ z (sampledCurvature τ routine z w.1) b w.2.1)
        (sampledRefreshAnchor P f q Lip s τ δ z (sampledCurvature τ routine z w.1) b w.2.2) := by
  constructor
  · intro hg
    constructor
    · intro hr hn
      by_contra hh
      exact hg (Or.inl ⟨⟨hr,hn⟩,hh⟩)
    · intro hr
      constructor
      · intro i hi
        apply le_of_not_gt
        intro hh
        exact hg (Or.inr ⟨hr,Or.inl ⟨i,hi,hh⟩⟩)
      · intro he
        apply le_of_not_gt
        intro hh
        exact hg (Or.inr ⟨hr,Or.inr ⟨he,hh⟩⟩)
  · intro hg hh
    rcases hh with ⟨⟨hr,hn⟩,hc⟩ | ⟨hr,hpost⟩
    · exact hc (hg.1 hr hn)
    · rcases hpost with ⟨i,hi,hc⟩ | ⟨he,ha⟩
      · exact not_lt_of_ge ((hg.2 hr).1 i hi) hc
      · exact not_lt_of_ge ((hg.2 hr).2 he) ha

variable {Ω Ψ A : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ] [MeasurableSpace A] {d L : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.sampledStepFailure_measurableSet (h : CommonLoss μ P ν F f)
    (q : ℕ) (Lip s τ γ ρ δ : ℝ) {routine : Point d → Ψ → CurvatureReply d}
    (hm : Measurable (fun w : Point d × Ψ => routine w.1 w.2))
    {z : A → TrackedState d L} {b : A → Bool} {tape : A → TrackingStepTape Ω Ψ P L τ δ}
    (hz : Measurable z) (hb : Measurable b) (hw : Measurable tape) :
    MeasurableSet {a | sampledStepFailure F P f q Lip s τ γ ρ δ routine (z a) (b a) (tape a)} := by
  have hr := sampledCurvature_measurable τ hm hz hw.fst
  have hp := (state_measurable_fields.mp (tracked_measurable_fields.mp hz).1).1
  have hv : MeasurableSet {a | ValidCurvatureReply F γ (z a).physical.point
      (sampledCurvature τ routine (z a) (tape a).1)} := by
    simp only [validCurvatureReply_iff_rayleigh]
    exact rayleighReplyValid_measurableSet γ ((continuous_hessian h.population_smooth).measurable.comp hp) hr
  exact ((trackedCurvatureNeeded_measurableSet τ hz).inter hv.compl).union
    (h.sampledPostFailure_measurableSet q Lip s τ ρ δ hz hr hb hw.snd)

/-- One complete step under a fresh curvature tape followed by independent
post-move samples. The explicit curvature slice hypothesis is the still
unimplemented eigensolver contract. Actual call count is retained inside
the expectation, including zero post-move work after a certificate. -/
theorem CommonLoss.sampledStepFailure_confidence (h : CommonLoss μ P ν F f)
    {η : Measure Ψ} [IsProbabilityMeasure η] (q : ℕ) (Lip s γ : ℝ)
    {τ ρ δ : ℝ} (hτ : 0 < τ) (hρ : 0 < ρ) (hδ : 0 < δ)
    {routine : Point d → Ψ → CurvatureReply d}
    (hm : Measurable (fun w : Point d × Ψ => routine w.1 w.2))
    (hc : ∀ x, η {w | ¬ValidCurvatureReply F γ x (routine x w)} ≤ ENNReal.ofReal δ)
    (z : TrackedState d L) (b : Bool) :
    trackingStepLaw μ η P L τ δ {w | sampledStepFailure F P f q Lip s τ γ ρ δ routine z b w} ≤
      ∫⁻ w, (sampledStepCallCount q Lip s τ routine z b w.1 : ℝ≥0∞)*ENNReal.ofReal δ
        ∂trackingStepLaw μ η P L τ δ := by
  let C := {w : Ψ | trackedCurvatureNeeded τ z ∧
    ¬ValidCurvatureReply F γ z.physical.point (sampledCurvature τ routine z w)}
  let D := {w : TrackingStepTape Ω Ψ P L τ δ |
    sampledPostFailure F P f q Lip s τ ρ δ z (sampledCurvature τ routine z w.1) b w.2}
  let c : ℝ≥0∞ := (if trackedCurvatureNeeded τ z then 1 else 0 : ℕ)*ENNReal.ofReal δ
  let p := fun w : Ψ => ENNReal.ofReal ((postCallCount q Lip s τ z (sampledCurvature τ routine z w) b : ℝ)*δ)
  have hr : Measurable (fun w : Ψ => sampledCurvature τ routine z w) :=
    sampledCurvature_measurable τ hm measurable_const measurable_id
  have hp : Measurable p := by
    have hn : Measurable (fun w : Ψ => postCallCount q Lip s τ z (sampledCurvature τ routine z w) b) :=
      postCallCount_measurable q Lip s τ measurable_const hr measurable_const
    exact Measurable.ennreal_ofReal (((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hn).mul_const δ)
  have hcurv : η C ≤ c := by
    by_cases he : trackedCurvatureNeeded τ z
    · simpa [C,c,sampledCurvature,he] using hc z.physical.point
    · simp [C,c,he]
  have hpost : (η.prod (postMoveLaw μ P L τ δ)) D ≤ ∫⁻ w, p w ∂η := by
    simpa only [Set.mem_univ,true_and,Measure.restrict_univ] using
      h.sampledPostFailure_past_confidence (η := η) q Lip s hτ hρ hδ
        (z := fun _ : Ψ => z) (r := fun w => sampledCurvature τ routine z w) (b := fun _ => b)
        measurable_const hr measurable_const MeasurableSet.univ
  have he : {w | sampledStepFailure F P f q Lip s τ γ ρ δ routine z b w} =
      (C ×ˢ Set.univ) ∪ D := by
    ext w
    simp only [sampledStepFailure,C,D,Set.mem_setOf_eq,Set.mem_union,Set.mem_prod,Set.mem_univ,and_true]
  have hmcharge : Measurable (fun w : TrackingStepTape Ω Ψ P L τ δ => c+p w.1) :=
    measurable_const.add (hp.comp measurable_fst)
  calc
    _ ≤ c+∫⁻ w, p w ∂η := by
      rw [he,trackingStepLaw]
      apply (measure_union_le _ _).trans
      apply add_le_add _ hpost
      simpa only [Measure.prod_prod,measure_univ,mul_one] using hcurv
    _ = ∫⁻ w : TrackingStepTape Ω Ψ P L τ δ, c+p w.1 ∂trackingStepLaw μ η P L τ δ := by
      rw [trackingStepLaw,lintegral_prod _ hmcharge.aemeasurable]
      simp only [lintegral_const,measure_univ,mul_one]
      rw [lintegral_add_left measurable_const]
      simp
    _ = _ := by
      apply lintegral_congr
      intro w
      simp only [c,p,sampledStepCallCount,Nat.cast_add,add_mul,
        ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast]

end
end SecondOrder
