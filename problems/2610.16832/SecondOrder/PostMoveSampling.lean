import SecondOrder.TrackedRequestCapping
import SecondOrder.BatchTape

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

/-- Independent fresh batch tapes for all possible direct chords. Only the
finite newly created node set is observed and charged at a move. -/
abbrev ChordPacketTape (Ω : Type*) (L : ℕ) (δ : ℝ) :=
  BinaryNode L → BatchTape (ℝ × Ω) (confidenceRepeats δ)

def chordPacketLaw {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (L : ℕ) (δ : ℝ) : Measure (ChordPacketTape Ω L δ) :=
  Measure.infinitePi (fun _ : BinaryNode L => batchTapeLaw (unitLine.prod μ) (confidenceRepeats δ))

instance chordPacketLaw_probability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (L : ℕ) (δ : ℝ) : IsProbabilityMeasure (chordPacketLaw μ L δ) := by
  unfold chordPacketLaw
  infer_instance

abbrev PostMoveTape (Ω : Type*) (P : Parameters) (L : ℕ) (τ δ : ℝ) :=
  ChordPacketTape Ω L δ × LocalDraws Ω (P.gradientNoise^2) (τ/4) δ

/-- The new chord batches are independent of one another and of the anchor
refresh batch. Taking a product with the old history fixes all endpoints
before any of these samples are observed. -/
def postMoveLaw {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (P : Parameters) (L : ℕ) (τ δ : ℝ) : Measure (PostMoveTape Ω P L τ δ) :=
  (chordPacketLaw μ L δ).prod (localLaw μ (P.gradientNoise^2) (τ/4) δ)

instance postMoveLaw_probability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (P : Parameters) (L : ℕ) (τ δ : ℝ) : IsProbabilityMeasure (postMoveLaw μ P L τ δ) := by
  unfold postMoveLaw
  infer_instance

def sampleChordAt {Ω : Type*} {d : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (x y : Point d) (ρ δ : ℝ) (w : BatchTape (ℝ × Ω) (confidenceRepeats δ)) : Point d :=
  adaptiveChord P f Prod.fst Prod.snd ρ δ ((x,y),w)

def sampledChordPacket {Ω : Type*} {d L : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (Lip s τ ρ δ : ℝ) (z : TrackedState d L) (r : CurvatureReply d) (b : Bool)
    (w : ChordPacketTape Ω L δ) (i : BinaryNode L) : Point d :=
  let p := trackedNext Lip s τ z r b
  if p.running = true ∧ i ∈ createdNodes L z.memory.length then
    sampleChordAt P f (trackerPushPoints z.memory p.point (nodeLeft i))
      (trackerPushPoints z.memory p.point (nodeRight i)) ρ δ (w i)
  else 0

def sampledRefreshAnchor {Ω : Type*} {d L : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (q : ℕ) (Lip s τ δ : ℝ) (z : TrackedState d L) (r : CurvatureReply d) (b : Bool)
    (w : LocalDraws Ω (P.gradientNoise^2) (τ/4) δ) : Point d :=
  if (trackedNext Lip s τ z r b).running = true ∧ trackedRestart q τ z r then
    gradientAnchor P f (trackedNext Lip s τ z r b).point (τ/4) δ w else 0

def sampledPostStep {Ω : Type*} {d L : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (q : ℕ) (Lip s τ ρ δ : ℝ) (z : TrackedState d L) (r : CurvatureReply d) (b : Bool)
    (w : PostMoveTape Ω P L τ δ) : TrackedState d L :=
  trackedStep q Lip s τ z r b (sampledChordPacket P f Lip s τ ρ δ z r b w.1)
    (sampledRefreshAnchor P f q Lip s τ δ z r b w.2)

def sampledInitial {Ω : Type*} {d L : ℕ} (P : Parameters) (f : Ω → Point d → ℝ) (τ δ : ℝ)
    (w : LocalDraws Ω (P.gradientNoise^2) (τ/4) δ) : TrackedState d L :=
  trackedInitial (gradientAnchor P f 0 (τ/4) δ w)

theorem sampledChordPacket_active {Ω : Type*} {d L : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (Lip s τ ρ δ : ℝ) (z : TrackedState d L) (r : CurvatureReply d) (b : Bool)
    (w : ChordPacketTape Ω L δ) (i : BinaryNode L)
    (hr : (trackedNext Lip s τ z r b).running = true) (hi : i ∈ createdNodes L z.memory.length) :
    sampledChordPacket P f Lip s τ ρ δ z r b w i =
      sampleChordAt P f (trackerPushPoints z.memory (trackedNext Lip s τ z r b).point (nodeLeft i))
        (trackerPushPoints z.memory (trackedNext Lip s τ z r b).point (nodeRight i)) ρ δ (w i) := by
  simp [sampledChordPacket,hr,hi]

theorem sampledRefreshAnchor_active {Ω : Type*} {d L : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (q : ℕ) (Lip s τ δ : ℝ) (z : TrackedState d L) (r : CurvatureReply d) (b : Bool)
    (w : LocalDraws Ω (P.gradientNoise^2) (τ/4) δ)
    (hr : (trackedNext Lip s τ z r b).running = true) (he : trackedRestart q τ z r) :
    sampledRefreshAnchor P f q Lip s τ δ z r b w =
      gradientAnchor P f (trackedNext Lip s τ z r b).point (τ/4) δ w := by
  simp [sampledRefreshAnchor,hr,he]

theorem chordPacketLaw_eval {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (L : ℕ) (δ : ℝ) (i : BinaryNode L)
    {s : Set (BatchTape (ℝ × Ω) (confidenceRepeats δ))} (hs : MeasurableSet s) :
    chordPacketLaw μ L δ ((fun w => w i) ⁻¹' s) =
      batchTapeLaw (unitLine.prod μ) (confidenceRepeats δ) s :=
  infinitePi_eval_preimage _ i hs

theorem postMoveLaw_chord_eval {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (P : Parameters) (L : ℕ) (τ δ : ℝ) (i : BinaryNode L)
    {s : Set (BatchTape (ℝ × Ω) (confidenceRepeats δ))} (hs : MeasurableSet s) :
    postMoveLaw μ P L τ δ {w | w.1 i ∈ s} = batchTapeLaw (unitLine.prod μ) (confidenceRepeats δ) s := by
  have he : {w : PostMoveTape Ω P L τ δ | w.1 i ∈ s} = ((fun w => w i) ⁻¹' s) ×ˢ Set.univ := by
    ext w
    simp
  rw [he,postMoveLaw,Measure.prod_prod]
  simp only [measure_univ,mul_one,chordPacketLaw_eval μ L δ i hs]

theorem postMoveLaw_anchor_eval {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (P : Parameters) (L : ℕ) (τ δ : ℝ)
    (s : Set (LocalDraws Ω (P.gradientNoise^2) (τ/4) δ)) :
    postMoveLaw μ P L τ δ {w | w.2 ∈ s} = localLaw μ (P.gradientNoise^2) (τ/4) δ s := by
  have he : {w : PostMoveTape Ω P L τ δ | w.2 ∈ s} = Set.univ ×ˢ s := by ext w; simp
  rw [he,postMoveLaw,Measure.prod_prod]
  simp

end
end SecondOrder
