import SecondOrder.OracleProgramCollection
import SecondOrder.AdaptiveChordProgram
import SecondOrder.PostMoveQueries

open MeasureTheory
open scoped Classical BigOperators

namespace SecondOrder
noncomputable section

abbrev PostChordSeed (L : ℕ) (δ : ℝ) := BinaryNode L → BatchTape ℝ (confidenceRepeats δ)

abbrev PostProgramInput (d L : ℕ) (δ : ℝ) :=
  TrackedState d L × CurvatureReply d × Bool × PostChordSeed L δ

def postChordNodeProgram {d L : ℕ} (P : Parameters) (Lip s τ ρ δ : ℝ)
    (w : PostProgramInput d L δ) (i : BinaryNode L) :
    OracleProgram (HvpQuery d) (Point d) (Point d) :=
  adaptiveChordProgram P ρ δ
    (trackerPushPoints w.1.memory (trackedNext Lip s τ w.1 w.2.1 w.2.2.1).point (nodeLeft i),
     trackerPushPoints w.1.memory (trackedNext Lip s τ w.1 w.2.1 w.2.2.1).point (nodeRight i),w.2.2.2 i)

def postChordNodeCost {d L : ℕ} (P : Parameters) (Lip s τ ρ δ : ℝ)
    (w : PostProgramInput d L δ) (i : BinaryNode L) : ℕ :=
  localQueryCount (chordVariance P
    (trackerPushPoints w.1.memory (trackedNext Lip s τ w.1 w.2.1 w.2.2.1).point (nodeLeft i))
    (trackerPushPoints w.1.memory (trackedNext Lip s τ w.1 w.2.1 w.2.2.1).point (nodeRight i))) ρ δ

theorem postChordNodeProgram_usesExactly {d L : ℕ} (P : Parameters) (Lip s τ ρ δ : ℝ)
    (w : PostProgramInput d L δ) (i : BinaryNode L) :
    OracleProgram.UsesExactly (postChordNodeCost P Lip s τ ρ δ w i)
      (postChordNodeProgram P Lip s τ ρ δ w i) := by
  have hh := adaptiveChordProgram_usesExactly P ρ δ
    (trackerPushPoints w.1.memory (trackedNext Lip s τ w.1 w.2.1 w.2.2.1).point (nodeLeft i),
     trackerPushPoints w.1.memory (trackedNext Lip s τ w.1 w.2.1 w.2.2.1).point (nodeRight i),w.2.2.2 i)
  exact hh

theorem postChordNodeProgram_measurable {d L : ℕ} (P : Parameters) (Lip s τ ρ δ : ℝ)
    (i : BinaryNode L) :
    OracleProgram.MeasurableFamily (.grad 0) 0
      (fun w : PostProgramInput d L δ => postChordNodeProgram P Lip s τ ρ δ w i) := by
  have hn := state_measurable_fields.mp (trackedNext_measurable Lip s τ
    (measurable_fst : Measurable (fun w : PostProgramInput d L δ => w.1))
    measurable_snd.fst measurable_snd.snd.fst)
  have hm := (tracked_measurable_fields.mp
    (measurable_fst : Measurable (fun w : PostProgramInput d L δ => w.1))).2.2
  have hp := trackerPushPoints_measurable hm hn.1
  exact (adaptiveChordProgram_measurable P ρ δ).comp _
    ((hp.eval (a := nodeLeft i)).prodMk ((hp.eval (a := nodeRight i)).prodMk
      (measurable_snd.snd.snd.eval (a := i))))

def postChordPacketProgram {d L : ℕ} (P : Parameters) (Lip s τ ρ δ : ℝ)
    (w : PostProgramInput d L δ) : OracleProgram (HvpQuery d) (Point d) (BinaryNode L → Point d) :=
  if (trackedNext Lip s τ w.1 w.2.1 w.2.2.1).running then
    OracleProgram.collectList 0 (postChordNodeProgram P Lip s τ ρ δ w)
      (createdNodes L w.1.memory.length).toList
  else .done 0

theorem postChordPacketProgram_measurable {d L : ℕ} (P : Parameters) (Lip s τ ρ δ : ℝ) :
    OracleProgram.MeasurableFamily (.grad 0) 0 (@postChordPacketProgram d L P Lip s τ ρ δ) := by
  have hm := (tracked_measurable_fields.mp
    (measurable_fst : Measurable (fun w : PostProgramInput d L δ => w.1))).2.2
  have hl := (trackerMemory_measurable_fields.mp hm).1
  have hn := state_measurable_fields.mp (trackedNext_measurable Lip s τ
    (measurable_fst : Measurable (fun w : PostProgramInput d L δ => w.1))
    measurable_snd.fst measurable_snd.snd.fst)
  have hp := OracleProgram.MeasurableFamily.chooseNat
    (fun (t : ℕ) (w : PostProgramInput d L δ) => OracleProgram.collectList 0
      (postChordNodeProgram P Lip s τ ρ δ w) (createdNodes L t).toList)
    (fun t => OracleProgram.collectList_measurable (HvpQuery.grad (0 : Point d)) (0 : Point d)
      (postChordNodeProgram P Lip s τ ρ δ)
      (postChordNodeProgram_measurable P Lip s τ ρ δ) (createdNodes L t).toList)
    (fun w => w.1.memory.length) hl
  have hd := OracleProgram.measurableFamily_done (Y := Point d) (HvpQuery.grad (0 : Point d))
    (0 : BinaryNode L → Point d) (fun _ : PostProgramInput d L δ => (0 : BinaryNode L → Point d)) measurable_const
  have hh := hp.ite hd {w : PostProgramInput d L δ | (trackedNext Lip s τ w.1 w.2.1 w.2.2.1).running=true}
    (hn.2.1 (measurableSet_singleton true))
  exact hh

theorem postChordPacketProgram_usesExactly {d L : ℕ} (P : Parameters) (Lip s τ ρ δ : ℝ)
    (w : PostProgramInput d L δ) :
    OracleProgram.UsesExactly (Fintype.card (PostChordSlot P Lip s τ ρ δ w.1 w.2.1 w.2.2.1))
      (postChordPacketProgram P Lip s τ ρ δ w) := by
  rw [postChordCall_count P 0]
  change OracleProgram.UsesExactly
    (requestCharge (chordRequestCharge (fun x y => localQueryCount (chordVariance P x y) ρ δ)) _) _
  rw [trackedStepRequests_chordCharge]
  unfold postChordPacketProgram
  split_ifs with hr
  · have hh := OracleProgram.collectList_usesExactly (0 : Point d)
      (postChordNodeProgram P Lip s τ ρ δ w)
      (postChordNodeCost P Lip s τ ρ δ w)
      (postChordNodeProgram_usesExactly P Lip s τ ρ δ w)
      (createdNodes L w.1.memory.length).toList
    simpa only [Finset.sum_map_toList,postChordNodeCost] using hh
  · trivial

end
end SecondOrder
