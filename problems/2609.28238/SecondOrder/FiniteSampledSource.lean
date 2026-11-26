import SecondOrder.TrackedPrefix

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

theorem drawsVector_last {E : Type*} (N : ℕ) (w : Draws E (N+1)) :
    drawsVector id (N+1) w ⟨N,Nat.lt_succ_self N⟩ = w.2 :=
  Fin.snoc_last _ _

/-- Finite sampled providers read only their own step coordinate. Values
beyond the finite horizon are inert padding; the analysis correction may
replace them, and no sample of an empty space is chosen for padding. -/
def finiteSampledSource {Ω Ψ : Type*} {d L : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (q : ℕ) (Lip s τ ρ δ : ℝ) (routine : Point d → Ψ → CurvatureReply d)
    (g : Point d) (N : ℕ) (w : Draws (TrackingStepTape Ω Ψ P L τ δ) N) : TrackingSource d L where
  initialAnchor := g
  curvature := fun t _ z => if ht : t < N then
    sampledCurvature τ routine z (drawsVector id N w ⟨t,ht⟩).1 else .certificate
  chords := fun t b z r => if ht : t < N then
    sampledChordPacket P f Lip s τ ρ δ z r (b (Fin.last t)) (drawsVector id N w ⟨t,ht⟩).2.1 else 0
  refresh := fun t b z r => if ht : t < N then
    sampledRefreshAnchor P f q Lip s τ δ z r (b (Fin.last t)) (drawsVector id N w ⟨t,ht⟩).2.2 else 0

theorem finiteSampledSource_extend {Ω Ψ : Type*} {d L : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (q : ℕ) (Lip s τ ρ δ : ℝ) (routine : Point d → Ψ → CurvatureReply d)
    (g : Point d) (N : ℕ) (w : Draws (TrackingStepTape Ω Ψ P L τ δ) (N+1)) :
    (finiteSampledSource P f q Lip s τ ρ δ routine g (N+1) w).AgreesBefore
      (finiteSampledSource P f q Lip s τ ρ δ routine g N w.1) N := by
  refine ⟨rfl,?_⟩
  intro t ht
  have ht' : t < N+1 := by omega
  have hw : drawsVector id (N+1) w ⟨t,ht'⟩ = drawsVector id N w.1 ⟨t,ht⟩ := by
    exact Fin.snoc_castSucc _ _ ⟨t,ht⟩
  constructor
  · funext b z
    simp only [finiteSampledSource,ht,ht',↓reduceDIte,hw]
  · constructor <;> funext b z r <;> simp only [finiteSampledSource,ht,ht',↓reduceDIte,hw]

variable {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ] {d L : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.finiteSampledSource_measurable (h : CommonLoss μ P ν F f)
    (q : ℕ) (Lip s τ ρ δ : ℝ) {routine : Point d → Ψ → CurvatureReply d}
    (hm : Measurable (fun w : Point d × Ψ => routine w.1 w.2)) (N : ℕ) :
    MeasurableTrackingSource (fun w : Point d × Draws (TrackingStepTape Ω Ψ P L τ δ) N =>
      finiteSampledSource P f q Lip s τ ρ δ routine w.1 N w.2) := by
  refine ⟨measurable_fst,?_,?_,?_⟩
  · intro t
    by_cases ht : t < N
    · simp only [finiteSampledSource,ht,↓reduceDIte]
      exact sampledCurvature_measurable τ hm measurable_snd
        (((drawsVector_measurable measurable_id N).comp measurable_fst.fst.snd).eval (a := ⟨t,ht⟩)).fst
    · simpa only [finiteSampledSource,ht,↓reduceDIte] using
        (measurable_const : Measurable (fun _ : ((Point d × Draws (TrackingStepTape Ω Ψ P L τ δ) N) ×
          (Fin t → Bool)) × TrackedState d L => (CurvatureReply.certificate : CurvatureReply d)))
  · intro t
    by_cases ht : t < N
    · simp only [finiteSampledSource,ht,↓reduceDIte]
      exact h.sampledChordPacket_measurable Lip s τ ρ δ measurable_fst.snd measurable_snd
        (measurable_fst.fst.snd.eval (a := Fin.last t))
        (((drawsVector_measurable measurable_id N).comp measurable_fst.fst.fst.snd).eval (a := ⟨t,ht⟩)).snd.fst
    · simp only [finiteSampledSource,ht,↓reduceDIte]
      exact measurable_const
  · intro t
    by_cases ht : t < N
    · simp only [finiteSampledSource,ht,↓reduceDIte]
      exact h.sampledRefreshAnchor_measurable q Lip s τ δ measurable_fst.snd measurable_snd
        (measurable_fst.fst.snd.eval (a := Fin.last t))
        (((drawsVector_measurable measurable_id N).comp measurable_fst.fst.fst.snd).eval (a := ⟨t,ht⟩)).snd.snd
    · simp only [finiteSampledSource,ht,↓reduceDIte]
      exact measurable_const

end
end SecondOrder
