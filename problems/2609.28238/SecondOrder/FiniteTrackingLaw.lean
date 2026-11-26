import SecondOrder.FreshTrackedConfidence

open MeasureTheory
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section

theorem MeasurableTrackingSource.comp {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {d L : ℕ} {source : A → TrackingSource d L} (hm : MeasurableTrackingSource source)
    {f : B → A} (hf : Measurable f) : MeasurableTrackingSource (fun b => source (f b)) := by
  refine ⟨hm.initialAnchor.comp hf,?_,?_,?_⟩
  · intro t
    exact (hm.curvature t).comp
      (((hf.comp measurable_fst.fst).prodMk measurable_fst.snd).prodMk measurable_snd)
  · intro t
    exact (hm.chords t).comp
      ((((hf.comp measurable_fst.fst.fst).prodMk measurable_fst.fst.snd).prodMk measurable_fst.snd).prodMk measurable_snd)
  · intro t
    exact (hm.refresh t).comp
      ((((hf.comp measurable_fst.fst.fst).prodMk measurable_fst.fst.snd).prodMk measurable_fst.snd).prodMk measurable_snd)

abbrev FiniteTrackingTape (Ω Ψ : Type*) (P : Parameters) (L : ℕ) (τ δ : ℝ) (N : ℕ) :=
  LocalDraws Ω (P.gradientNoise^2) (τ/4) δ × Draws (TrackingStepTape Ω Ψ P L τ δ) N

def finiteTrackingLaw {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (η : Measure Ψ) (P : Parameters) (L : ℕ) (τ δ : ℝ) (N : ℕ) :
    Measure (FiniteTrackingTape Ω Ψ P L τ δ N) :=
  (localLaw μ (P.gradientNoise^2) (τ/4) δ).prod (drawsLaw (trackingStepLaw μ η P L τ δ) N)

instance finiteTrackingLaw_probability {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (η : Measure Ψ) [IsProbabilityMeasure η]
    (P : Parameters) (L : ℕ) (τ δ : ℝ) (N : ℕ) : IsProbabilityMeasure (finiteTrackingLaw μ η P L τ δ N) := by
  unfold finiteTrackingLaw
  infer_instance

/-- A finite actual sampled source, including its independently sampled
initial anchor. This is the source used for the finite algorithm bounds. -/
def finiteActualSource {Ω Ψ : Type*} {d L : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (q : ℕ) (Lip s τ ρ δ : ℝ) (routine : Point d → Ψ → CurvatureReply d) (N : ℕ)
    (w : FiniteTrackingTape Ω Ψ P L τ δ N) : TrackingSource d L :=
  finiteSampledSource P f q Lip s τ ρ δ routine (gradientAnchor P f 0 (τ/4) δ w.1) N w.2

variable {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ] {d L : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.finiteActualSource_measurable (h : CommonLoss μ P ν F f)
    (q : ℕ) (Lip s τ ρ δ : ℝ) {routine : Point d → Ψ → CurvatureReply d}
    (hm : Measurable (fun w : Point d × Ψ => routine w.1 w.2)) (N : ℕ) :
    MeasurableTrackingSource (finiteActualSource (L := L) P f q Lip s τ ρ δ routine N) :=
  (h.finiteSampledSource_measurable q Lip s τ ρ δ hm N).comp
    (((h.anchor_measurable 0 (τ/4) δ).comp measurable_fst).prodMk measurable_snd)

/-- The initial anchor is charged exactly once, and every later step is
charged by its actual local request count. This bound is uniform over
the fixed sign path, so independent random signs can be mixed afterward. -/
theorem CommonLoss.finiteTrackingLaw_failure_slice (h : CommonLoss μ P ν F f)
    {η : Measure Ψ} [IsProbabilityMeasure η] {q : ℕ} (hq : 0 < q) (Lip s γ : ℝ)
    {τ ρ δ : ℝ} (hτ : 0 < τ) (hρ : 0 < ρ) (hδ : 0 < δ)
    {routine : Point d → Ψ → CurvatureReply d}
    (hm : Measurable (fun w : Point d × Ψ => routine w.1 w.2))
    (hc : ∀ x, η {w | ¬ValidCurvatureReply F γ x (routine x w)} ≤ ENNReal.ofReal δ)
    (β : ℕ → Bool) (N : ℕ) :
    finiteTrackingLaw μ η P L τ δ N
      {w | ¬trackedHistoryGood F q Lip s τ γ ρ (finiteActualSource P f q Lip s τ ρ δ routine N w) N (fun i => β i.val)} ≤
        ENNReal.ofReal (((4*N+2 : ℕ) : ℝ)*δ) := by
  let C := {a : LocalDraws Ω (P.gradientNoise^2) (τ/4) δ |
    τ/4 < ‖gradientAnchor P f 0 (τ/4) δ a-gradient F 0‖}
  let B := ENNReal.ofReal (((4*N+1 : ℕ) : ℝ)*δ)
  have hC : MeasurableSet C :=
    measurableSet_lt measurable_const ((h.anchor_measurable 0 (τ/4) δ).sub_const (gradient F 0)).norm
  have hb : MeasurableSet {w : FiniteTrackingTape Ω Ψ P L τ δ N |
      ¬trackedHistoryGood F q Lip s τ γ ρ (finiteActualSource P f q Lip s τ ρ δ routine N w) N (fun i => β i.val)} :=
    ((trackedHistoryGood_measurableSet h.population_smooth q Lip s τ γ ρ
      (h.finiteActualSource_measurable q Lip s τ ρ δ hm N) N).preimage
        (measurable_id.prodMk measurable_const)).compl
  rw [finiteTrackingLaw,Measure.prod_apply hb]
  calc
    _ ≤ ∫⁻ a, C.indicator (fun _ => (1 : ℝ≥0∞)) a+B ∂localLaw μ (P.gradientNoise^2) (τ/4) δ := by
      apply lintegral_mono
      intro a
      by_cases ha : a ∈ C
      · simp only [Set.indicator_of_mem ha]
        exact (measure_mono (Set.subset_univ _)).trans (by simp)
      · simp only [Set.indicator_of_not_mem ha,zero_add]
        have hg : ‖gradientAnchor P f 0 (τ/4) δ a-gradient F 0‖ ≤ τ/4 := le_of_not_gt ha
        change drawsLaw (trackingStepLaw μ η P L τ δ) N
          {w | ¬trackedHistoryGood F q Lip s τ γ ρ
            (finiteActualSource P f q Lip s τ ρ δ routine N (a,w)) N (fun i => β i.val)} ≤ B
        simpa only [finiteActualSource,freshTrackedHistoryGood_iff,hg,true_and,B] using
          h.freshTrackedFailure_bound (η := η) (L := L) hq Lip s γ hτ hρ hδ hm hc
            (gradientAnchor P f 0 (τ/4) δ a) β N
    _ = localLaw μ (P.gradientNoise^2) (τ/4) δ C+B := by
      rw [lintegral_add_left (measurable_const.indicator hC),lintegral_indicator hC]
      simp
    _ ≤ ENNReal.ofReal δ+B := add_le_add_right (h.anchor_confidence 0 (by positivity) hδ) _
    _ = _ := by
      dsimp only [B]
      rw [← ENNReal.ofReal_add hδ.le (mul_nonneg (Nat.cast_nonneg _) hδ.le)]
      congr 1
      push_cast
      ring

end
end SecondOrder
