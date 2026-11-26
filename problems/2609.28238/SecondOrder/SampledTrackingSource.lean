import SecondOrder.PostMoveQueries
import SecondOrder.FreshCallWeighted

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

/-- A fresh curvature routine tape followed by the independent post-move
chord and anchor tapes. Signs are kept separate in the existing sign law. -/
abbrev TrackingStepTape (Ω Ψ : Type*) (P : Parameters) (L : ℕ) (τ δ : ℝ) :=
  Ψ × PostMoveTape Ω P L τ δ

abbrev TrackingTape (Ω Ψ : Type*) (P : Parameters) (L : ℕ) (τ δ : ℝ) :=
  LocalDraws Ω (P.gradientNoise^2) (τ/4) δ × (ℕ → TrackingStepTape Ω Ψ P L τ δ)

def trackingStepLaw {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (η : Measure Ψ) (P : Parameters) (L : ℕ) (τ δ : ℝ) :
    Measure (TrackingStepTape Ω Ψ P L τ δ) := η.prod (postMoveLaw μ P L τ δ)

instance trackingStepLaw_probability {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (η : Measure Ψ) [IsProbabilityMeasure η]
    (P : Parameters) (L : ℕ) (τ δ : ℝ) : IsProbabilityMeasure (trackingStepLaw μ η P L τ δ) := by
  unfold trackingStepLaw
  infer_instance

def trackingTapeLaw {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (η : Measure Ψ) [IsProbabilityMeasure η]
    (P : Parameters) (L : ℕ) (τ δ : ℝ) : Measure (TrackingTape Ω Ψ P L τ δ) :=
  (localLaw μ (P.gradientNoise^2) (τ/4) δ).prod
    (Measure.infinitePi (fun _ : ℕ => trackingStepLaw μ η P L τ δ))

instance trackingTapeLaw_probability {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (η : Measure Ψ) [IsProbabilityMeasure η]
    (P : Parameters) (L : ℕ) (τ δ : ℝ) : IsProbabilityMeasure (trackingTapeLaw μ η P L τ δ) := by
  unfold trackingTapeLaw
  infer_instance

def sampledCurvature {Ψ : Type*} {d L : ℕ} (τ : ℝ)
    (routine : Point d → Ψ → CurvatureReply d) (z : TrackedState d L) (w : Ψ) : CurvatureReply d :=
  if trackedCurvatureNeeded τ z then routine z.physical.point w else .certificate

/-- Concrete anchor and chord providers read their own fresh step tape.
The curvature implementation remains an explicit input routine; no
eigensolver correctness or price is asserted by this definition. -/
def sampledTrackingSource {Ω Ψ : Type*} {d L : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (q : ℕ) (Lip s τ ρ δ : ℝ) (routine : Point d → Ψ → CurvatureReply d)
    (w : TrackingTape Ω Ψ P L τ δ) : TrackingSource d L where
  initialAnchor := gradientAnchor P f 0 (τ/4) δ w.1
  curvature := fun t _ z => sampledCurvature τ routine z (w.2 t).1
  chords := fun t b z r => sampledChordPacket P f Lip s τ ρ δ z r (b (Fin.last t)) (w.2 t).2.1
  refresh := fun t b z r => sampledRefreshAnchor P f q Lip s τ δ z r (b (Fin.last t)) (w.2 t).2.2

theorem trackedCurvatureNeeded_measurableSet {A : Type*} [MeasurableSpace A] {d L : ℕ}
    (τ : ℝ) {z : A → TrackedState d L} (hz : Measurable z) :
    MeasurableSet {a | trackedCurvatureNeeded τ (z a)} := by
  have hf := tracked_measurable_fields.mp hz
  have hp := state_measurable_fields.mp hf.1
  exact (hp.2.1 (measurableSet_singleton true)).inter
    (measurableSet_le (trackerRead_measurable hf.2.2).norm measurable_const)

theorem sampledCurvature_measurable {A Ψ : Type*} [MeasurableSpace A] [MeasurableSpace Ψ] {d L : ℕ}
    (τ : ℝ) {routine : Point d → Ψ → CurvatureReply d}
    (hr : Measurable (fun w : Point d × Ψ => routine w.1 w.2))
    {z : A → TrackedState d L} {tape : A → Ψ} (hz : Measurable z) (hw : Measurable tape) :
    Measurable (fun a => sampledCurvature τ routine (z a) (tape a)) := by
  have hp := (state_measurable_fields.mp (tracked_measurable_fields.mp hz).1).1
  exact Measurable.ite (trackedCurvatureNeeded_measurableSet τ hz)
    (hr.comp (hp.prodMk hw)) measurable_const

variable {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ] {d L : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.sampledTrackingSource_measurable (h : CommonLoss μ P ν F f)
    (q : ℕ) (Lip s τ ρ δ : ℝ) {routine : Point d → Ψ → CurvatureReply d}
    (hr : Measurable (fun w : Point d × Ψ => routine w.1 w.2)) :
    MeasurableTrackingSource (sampledTrackingSource (L := L) P f q Lip s τ ρ δ routine) := by
  refine ⟨(h.anchor_measurable 0 (τ/4) δ).comp measurable_fst,?_,?_,?_⟩
  · intro t
    exact sampledCurvature_measurable τ hr measurable_snd
      ((measurable_fst.fst.snd.eval (a := t)).fst)
  · intro t
    exact h.sampledChordPacket_measurable Lip s τ ρ δ measurable_fst.snd measurable_snd
      (measurable_fst.fst.snd.eval (a := Fin.last t))
      ((measurable_fst.fst.fst.snd.eval (a := t)).snd.fst)
  · intro t
    exact h.sampledRefreshAnchor_measurable q Lip s τ δ measurable_fst.snd measurable_snd
      (measurable_fst.fst.snd.eval (a := Fin.last t))
      ((measurable_fst.fst.fst.snd.eval (a := t)).snd.snd)

/-- Changing every unobserved future tape preserves the entire state, not
merely the current iterate. Curvature reads no new sign, while the
post-move tapes are used only after the endpoint has been fixed. -/
theorem sampledTrackingSource_causal (P : Parameters) (f : Ω → Point d → ℝ)
    (q : ℕ) (Lip s τ ρ δ : ℝ) (routine : Point d → Ψ → CurvatureReply d)
    (a : LocalDraws Ω (P.gradientNoise^2) (τ/4) δ)
    (u v : ℕ → TrackingStepTape Ω Ψ P L τ δ) (t : ℕ) (b : Fin t → Bool)
    (hp : ∀ k < t, u k = v k) :
    trackedRun q Lip s τ (sampledTrackingSource P f q Lip s τ ρ δ routine (a,u)) t b =
      trackedRun q Lip s τ (sampledTrackingSource P f q Lip s τ ρ δ routine (a,v)) t b := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ho := ih (Fin.init b) (fun k hk => hp k (by omega))
    have ht := hp t (by omega)
    simp only [trackedRun] at ho ⊢
    rw [ho]
    simp only [sampledTrackingSource]
    rw [ht]

theorem trackingTapeLaw_step {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (η : Measure Ψ) [IsProbabilityMeasure η]
    (P : Parameters) (L : ℕ) (τ δ : ℝ) (t : ℕ)
    {s : Set (TrackingStepTape Ω Ψ P L τ δ)} (hs : MeasurableSet s) :
    trackingTapeLaw μ η P L τ δ {w | w.2 t ∈ s} = trackingStepLaw μ η P L τ δ s := by
  have he : {w : TrackingTape Ω Ψ P L τ δ | w.2 t ∈ s} = Set.univ ×ˢ {w | w t ∈ s} := by
    ext w
    simp
  rw [he,trackingTapeLaw,Measure.prod_prod]
  simp only [measure_univ,one_mul]
  exact infinitePi_eval_preimage _ t hs

end
end SecondOrder
