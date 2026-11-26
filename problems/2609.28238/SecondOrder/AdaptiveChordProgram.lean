import SecondOrder.PrivateBatchTape
import SecondOrder.FreshChordOutputLaw
import SecondOrder.VariableOracleProgram
import SecondOrder.AdaptiveChord

open MeasureTheory
open scoped BigOperators

namespace SecondOrder
noncomputable section

abbrev ChordProgramInput (d : ℕ) (δ : ℝ) :=
  Point d × Point d × BatchTape ℝ (confidenceRepeats δ)

/-- Fixed-size branch of the adaptive chord program. Every query is an
HVP at a point computed from endpoints and private line positions. -/
def fixedSizeChordProgram {d : ℕ} (m : ℕ) (ρ δ : ℝ) (w : ChordProgramInput d δ) :
    OracleProgram (HvpQuery d) (Point d) (Point d) :=
  OracleProgram.batch (Fintype.card (Fin (confidenceRepeats δ) × Fin m))
    (fun k => let i := (Fintype.equivFin (Fin (confidenceRepeats δ) × Fin m)).symm k
      let u := drawsVector id m (drawsVector id (confidenceRepeats δ) (w.2.2 m) i.1) i.2
      .hvp (w.1+u•(w.2.1-w.1)) (w.2.1-w.1))
    (fun ys => robustCenter (confidenceRepeats_pos δ)
      (fun j => (m:ℝ)⁻¹ • ∑ i : Fin m, ys (Fintype.equivFin _ (j,i))) (ρ/3))

theorem fixedSizeChordProgram_measurable {d : ℕ} (m : ℕ) (ρ δ : ℝ) :
    OracleProgram.MeasurableFamily (.grad 0) 0 (@fixedSizeChordProgram d m ρ δ) := by
  apply OracleProgram.batch_measurable
  · intro k
    let i := (Fintype.equivFin (Fin (confidenceRepeats δ) × Fin m)).symm k
    have hu₀ := (nestedDrawsSlots_measurePreserving unitLine m (confidenceRepeats δ)).measurable.comp
      ((measurable_pi_apply m).comp (measurable_snd.snd : Measurable (fun w : ChordProgramInput d δ => w.2.2)))
    have hu := (measurable_pi_apply i).comp hu₀
    have hd : Measurable (fun w : ChordProgramInput d δ => w.2.1-w.1) :=
      measurable_snd.fst.sub measurable_fst
    have hx := measurable_fst.add (hu.smul hd)
    exact (hvpQueryMeasurableEquiv d).symm.measurable.comp
      (measurable_inr.comp (hx.prodMk hd))
  · apply (robustCenter_measurable (confidenceRepeats_pos δ) (ρ/3)).comp
    apply measurable_pi_lambda
    intro j
    have hm : Measurable (fun w : ChordProgramInput d δ ×
        (Fin (Fintype.card (Fin (confidenceRepeats δ) × Fin m)) → Point d) =>
        ∑ i : Fin m, w.2 (Fintype.equivFin _ (j,i))) :=
      Finset.measurable_sum _ (fun i _ =>
        (measurable_pi_apply (Fintype.equivFin _ (j,i))).comp measurable_snd)
    exact hm.const_smul ((m:ℝ)⁻¹)

def adaptiveChordProgram {d : ℕ} (P : Parameters) (ρ δ : ℝ) (w : ChordProgramInput d δ) :
    OracleProgram (HvpQuery d) (Point d) (Point d) :=
  fixedSizeChordProgram (localBatchSize (chordVariance P w.1 w.2.1) ρ) ρ δ w

theorem adaptiveChordProgram_measurable {d : ℕ} (P : Parameters) (ρ δ : ℝ) :
    OracleProgram.MeasurableFamily (.grad 0) 0 (@adaptiveChordProgram d P ρ δ) :=
  OracleProgram.MeasurableFamily.chooseNat (fun m => fixedSizeChordProgram m ρ δ)
    (fun m => fixedSizeChordProgram_measurable m ρ δ)
    (fun w => localBatchSize (chordVariance P w.1 w.2.1) ρ)
    (localBatchSize_measurable (chordVariance_measurable P measurable_fst measurable_snd.fst) ρ)

theorem adaptiveChordProgram_eq {d : ℕ} (P : Parameters) (ρ δ : ℝ) (w : ChordProgramInput d δ) :
    adaptiveChordProgram P ρ δ w=freshChordProgram P w.1 w.2.1 ρ δ
      (localPrivateSlots (chordVariance P w.1 w.2.1) ρ δ w.2.2) := rfl

theorem adaptiveChordProgram_usesExactly {d : ℕ} (P : Parameters) (ρ δ : ℝ)
    (w : ChordProgramInput d δ) :
    OracleProgram.UsesExactly (localQueryCount (chordVariance P w.1 w.2.1) ρ δ)
      (adaptiveChordProgram P ρ δ w) := by
  rw [adaptiveChordProgram_eq]
  exact freshChordProgram_usesExactly P w.1 w.2.1 ρ δ _

def adaptiveChordProgramAlgorithm {d : ℕ} (P : Parameters) (ρ δ : ℝ) (w : ChordProgramInput d δ) :
    HvpAlgorithm d (ℕ → Point d) :=
  OracleProgram.algorithm (.grad 0) 0 0 (adaptiveChordProgram P ρ δ w)

theorem adaptiveChordProgramAlgorithm_measurable {d : ℕ} (P : Parameters) (ρ δ : ℝ) :
    MeasurableOracleAlgorithmFamily (@adaptiveChordProgramAlgorithm d P ρ δ) :=
  OracleProgram.algorithm_measurable 0 (adaptiveChordProgram_measurable P ρ δ)

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P : Parameters} {d : ℕ} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

/-- For every state-selected pair of endpoints the same private source
and ordinary fresh oracle samples reproduce the original chord law. -/
theorem CommonLoss.adaptiveChordProgram_outputLaw (h : CommonLoss μ P ν F f)
    (a₀ : Ω) (x y : Point d) (ρ δ : ℝ) :
    OracleProgram.seededOutputLaw μ (batchTapeLaw unitLine (confidenceRepeats δ))
      (.grad 0) 0 (fun q z => hvpReply f z q) (fun u => adaptiveChordProgram P ρ δ (x,y,u))
      (localQueryCount (chordVariance P x y) ρ δ)=
      Measure.map (freshChord P f x y ρ δ) (localLaw (unitLine.prod μ) (chordVariance P x y) ρ δ) := by
  have hs := localPrivateSlots_measurePreserving unitLine (chordVariance P x y) ρ δ
  have ht := OracleProgram.seededOutputLaw_mapSeed μ (batchTapeLaw unitLine (confidenceRepeats δ))
    (.grad 0) 0 0 a₀ (fun q z => hvpReply f z q) h.hvpReply_joint_measurable
    (freshChordProgram P x y ρ δ) (freshChordProgram_measurable P x y ρ δ)
    (localPrivateSlots (chordVariance P x y) ρ δ) hs.measurable (localQueryCount (chordVariance P x y) ρ δ)
  rw [hs.map_eq] at ht
  have hp : (fun u => adaptiveChordProgram P ρ δ (x,y,u))=
      (fun u => freshChordProgram P x y ρ δ (localPrivateSlots (chordVariance P x y) ρ δ u)) := by
    funext u
    exact adaptiveChordProgram_eq P ρ δ (x,y,u)
  rw [hp,←ht,h.freshChordProgram_outputLaw a₀ x y ρ δ]

/-- Exact conditional output law matching the already analyzed adaptive
chord call, for every possible pair of history-dependent endpoints. -/
theorem CommonLoss.adaptiveChordProgram_slice_outputLaw (h : CommonLoss μ P ν F f)
    {A : Type} (a₀ : Ω) (x y : A → Point d) (a : A) (ρ δ : ℝ) :
    OracleProgram.seededOutputLaw μ (batchTapeLaw unitLine (confidenceRepeats δ))
      (.grad 0) 0 (fun q z => hvpReply f z q) (fun u => adaptiveChordProgram P ρ δ (x a,y a,u))
      (localQueryCount (chordVariance P (x a) (y a)) ρ δ)=
      Measure.map (fun v => adaptiveChord P f x y ρ δ (a,v))
        (batchTapeLaw (unitLine.prod μ) (confidenceRepeats δ)) := by
  rw [h.adaptiveChordProgram_outputLaw a₀ (x a) (y a) ρ δ]
  have he := batchTapeProjection_measurePreserving (unitLine.prod μ) (confidenceRepeats δ)
    (localBatchSize (chordVariance P (x a) (y a)) ρ)
  change Measure.map (freshChord P f (x a) (y a) ρ δ)
    (drawsLaw (drawsLaw (unitLine.prod μ) (localBatchSize (chordVariance P (x a) (y a)) ρ))
      (confidenceRepeats δ))=_
  rw [←he.map_eq,Measure.map_map (h.chord_measurable (x a) (y a) ρ δ) he.measurable]
  rfl

theorem CommonLoss.adaptiveChordProgram_confidence (h : CommonLoss μ P ν F f)
    (a₀ : Ω) (x y : Point d) {ρ δ : ℝ} (hρ : 0<ρ) (hδ : 0<δ) :
    (OracleProgram.seededOutputLaw μ (batchTapeLaw unitLine (confidenceRepeats δ))
      (.grad 0) 0 (fun q z => hvpReply f z q) (fun u => adaptiveChordProgram P ρ δ (x,y,u))
      (localQueryCount (chordVariance P x y) ρ δ))
      {g | ρ<‖g-(gradient F y-gradient F x)‖}≤ENNReal.ofReal δ := by
  have hs : MeasurableSet {g : Point d | ρ<‖g-(gradient F y-gradient F x)‖} :=
    measurableSet_lt measurable_const (measurable_id.sub_const _).norm
  rw [h.adaptiveChordProgram_outputLaw a₀ x y ρ δ,Measure.map_apply (h.chord_measurable x y ρ δ) hs]
  exact h.chord_confidence x y hρ hδ

theorem CommonLoss.adaptiveChordProgramAlgorithm_confidence (h : CommonLoss μ P ν F f)
    (a₀ : Ω) (x y : Point d) {ρ δ : ℝ} (hρ : 0<ρ) (hδ : 0<δ) :
    ((batchTapeLaw unitLine (confidenceRepeats δ)).prod
      (oracleHistoryLaw μ (localQueryCount (chordVariance P x y) ρ δ)))
      {w | ρ<‖oracleHistoryOutput (adaptiveChordProgramAlgorithm P ρ δ (x,y,w.1))
        (fun q z => hvpReply f z q) (localQueryCount (chordVariance P x y) ρ δ) w.2-
        (gradient F y-gradient F x)‖}≤ENNReal.ofReal δ := by
  have hp := (adaptiveChordProgram_measurable (d := d) P ρ δ).comp
    (fun u => (x,y,u)) (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hs : MeasurableSet {g : Point d | ρ<‖g-(gradient F y-gradient F x)‖} :=
    measurableSet_lt measurable_const (measurable_id.sub_const _).norm
  have he := OracleProgram.algorithm_seeded_history_event μ
    (batchTapeLaw unitLine (confidenceRepeats δ)) (.grad 0) 0 0 a₀
    (fun q z => hvpReply f z q) h.hvpReply_joint_measurable
    (fun u => adaptiveChordProgram P ρ δ (x,y,u)) hp (localQueryCount (chordVariance P x y) ρ δ)
    _ hs
  exact he.le.trans (h.adaptiveChordProgram_confidence a₀ x y hρ hδ)

end
end SecondOrder
