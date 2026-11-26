import SecondOrder.PostChordProgram
import SecondOrder.TrackedBudgetMeasurability

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

def postRefreshProgram {d L : ℕ} (P : Parameters) (q : ℕ) (Lip s τ δ : ℝ)
    (w : PostProgramInput d L δ) : OracleProgram (HvpQuery d) (Point d) (Point d) :=
  if (trackedNext Lip s τ w.1 w.2.1 w.2.2.1).running = true ∧ trackedRestart q τ w.1 w.2.1 then
    gradientAnchorProgram P (trackedNext Lip s τ w.1 w.2.1 w.2.2.1).point (τ/4) δ
  else .done 0

theorem postRefreshProgram_measurable {d L : ℕ} (P : Parameters) (q : ℕ) (Lip s τ δ : ℝ) :
    OracleProgram.MeasurableFamily (.grad 0) 0 (@postRefreshProgram d L P q Lip s τ δ) := by
  have hn := state_measurable_fields.mp (trackedNext_measurable Lip s τ
    (measurable_fst : Measurable (fun w : PostProgramInput d L δ => w.1))
    measurable_snd.fst measurable_snd.snd.fst)
  have hp := (gradientAnchorProgram_measurable (d := d) P (τ/4) δ).comp _ hn.1
  have hd := OracleProgram.measurableFamily_done (Y := Point d) (HvpQuery.grad (0 : Point d))
    (0 : Point d) (fun _ : PostProgramInput d L δ => (0 : Point d)) measurable_const
  have hh := hp.ite hd {w : PostProgramInput d L δ |
      (trackedNext Lip s τ w.1 w.2.1 w.2.2.1).running = true ∧ trackedRestart q τ w.1 w.2.1}
    ((hn.2.1 (measurableSet_singleton true)).inter
      (trackedRestart_measurableSet q τ measurable_fst measurable_snd.fst))
  exact hh

theorem postRefreshProgram_usesExactly {d L : ℕ} (P : Parameters) (q : ℕ) (Lip s τ δ : ℝ)
    (w : PostProgramInput d L δ) :
    OracleProgram.UsesExactly (Fintype.card (PostRefreshSlot P q Lip s τ δ w.1 w.2.1 w.2.2.1))
      (postRefreshProgram P q Lip s τ δ w) := by
  rw [postRefreshCall_count,trackedStepRequests_anchor]
  unfold postRefreshProgram
  split_ifs
  · rw [Nat.one_mul]
    exact localReplyProgram_usesExactly _ _ _ _
  · rw [Nat.zero_mul]
    trivial

/-- Every newly completed chord is evaluated before the optional refresh;
the final state receives only the resulting reply estimates. -/
def postMoveProgram {d L : ℕ} (P : Parameters) (q : ℕ) (Lip s τ ρ δ : ℝ)
    (w : PostProgramInput d L δ) : OracleProgram (HvpQuery d) (Point d) (TrackedState d L) :=
  OracleProgram.bind (postChordPacketProgram P Lip s τ ρ δ w) (fun packet =>
    OracleProgram.bind (postRefreshProgram P q Lip s τ δ w) (fun anchor =>
      .done (trackedStep q Lip s τ w.1 w.2.1 w.2.2.1 packet anchor)))

theorem postMoveProgram_measurable {d L : ℕ} (P : Parameters) (q : ℕ) (Lip s τ ρ δ : ℝ) :
    OracleProgram.MeasurableFamily (.grad 0) (trackedInitial 0)
      (@postMoveProgram d L P q Lip s τ ρ δ) := by
  apply (postChordPacketProgram_measurable P Lip s τ ρ δ).bind
  have hr := (postRefreshProgram_measurable P q Lip s τ δ).comp
    (fun w : PostProgramInput d L δ × (BinaryNode L → Point d) => w.1) measurable_fst
  apply hr.bind
  apply OracleProgram.measurableFamily_done
  exact trackedStep_measurable q Lip s τ measurable_fst.fst.fst
    measurable_fst.fst.snd.fst measurable_fst.fst.snd.snd.fst measurable_fst.snd measurable_snd

theorem postMoveProgram_usesExactly {d L : ℕ} (P : Parameters) (q : ℕ) (Lip s τ ρ δ : ℝ)
    (w : PostProgramInput d L δ) :
    OracleProgram.UsesExactly (postRequestPrice P q Lip s τ ρ δ w.1 w.2.1 w.2.2.1)
      (postMoveProgram P q Lip s τ ρ δ w) := by
  rw [postRequestPrice_eq_oracle_slots]
  apply (postChordPacketProgram_usesExactly P Lip s τ ρ δ w).bind
  intro packet
  have hh := (postRefreshProgram_usesExactly P q Lip s τ δ w).bind
    (fun anchor => .done (trackedStep q Lip s τ w.1 w.2.1 w.2.2.1 packet anchor))
    (M := 0) (fun _ => trivial)
  simpa only [Nat.add_zero] using hh

end
end SecondOrder
