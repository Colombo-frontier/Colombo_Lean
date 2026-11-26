import UpperProgramSlots
import UpperSmoothingSecant

/-! Exact execution semantics for the actual transcript-defined program. -/

namespace Task006.Full

namespace OracleAlgorithm

variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S]

theorem runPrefix_stable (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) {t u : ℕ} (htu : t ≤ u) (i : Fin N) (hi : i.val < t) :
    A.runPrefix F tape seed u i = A.runPrefix F tape seed t i := by
  induction u generalizing t with
  | zero => omega
  | succ u ih =>
    by_cases heq : t = u + 1
    · subst t; rfl
    · have htu' : t ≤ u := by omega
      rw [runPrefix]
      by_cases hu : u < N
      · rw [dif_pos hu, Function.update_of_ne (show i ≠ ⟨u, hu⟩ by
          intro he
          have := congrArg Fin.val he
          simp only [Fin.val_mk] at this
          omega)]
        exact ih htu' hi
      · rw [dif_neg hu]
        exact ih htu' hi

theorem runPrefix_new_reply (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (n : Fin N) :
    A.runPrefix F tape seed (n.val + 1) n =
      scalarReply F tape (A.action n seed (A.runPrefix F tape seed n.val)) := by
  rw [runPrefix, dif_pos n.isLt]
  exact Function.update_self n _ _

end OracleAlgorithm

theorem upperIterate_seed_past {d T : ℕ} (P : UpperProgramParameters)
    {seed seed' : UpperSeed d T} (h : Transcript (upperReplyCount d T)) (t : ℕ)
    (hh : ∀ j : Fin T, j.val < t → seed j = seed' j) :
    upperIterate P seed h t = upperIterate P seed' h t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hprev : ∀ j : Fin T, j.val < t → seed j = seed' j := fun j hj => hh j (by omega)
    rw [upperIterate, upperIterate]
    split_ifs with ht
    · rw [ih hprev, hh ⟨t, ht⟩ (Nat.lt_succ_self t)]
    · exact ih hprev

/-- Every recorded reply is exactly the sample value at the actual query point
on the paired handle. Past dependence allows the same point to be reconstructed
from the final transcript. -/
theorem upperProgram_final_reply {d T : ℕ} (P : UpperProgramParameters) (hd : 0 < d)
    {Ω : Type*} (F : Space d → Ω → ℝ) (tape : ℕ → Ω) (seed : UpperSeed d T)
    (n : Fin (upperReplyCount d T)) :
    (upperPairedProgram P hd).toAlgorithm.finalTranscript F tape seed n =
      F (upperQueryPoint P hd n seed
        ((upperPairedProgram P hd).toAlgorithm.finalTranscript F tape seed)) (tape (n.val / 2)) := by
  let A := (upperPairedProgram (T := T) P hd).toAlgorithm
  change A.runPrefix F tape seed (upperReplyCount d T) n = _
  rw [A.runPrefix_stable F tape seed (Nat.succ_le_of_lt n.isLt) n (Nat.lt_succ_self n.val),
    A.runPrefix_new_reply F tape seed n]
  change F (upperQueryPoint P hd n seed (A.runPrefix F tape seed n.val)) (tape (n.val / 2)) = _
  rw [upperQueryPoint_past P hd n seed (h := A.runPrefix F tape seed n.val)
    (h' := A.finalTranscript F tape seed)
    (fun i hi => (A.runPrefix_stable F tape seed (Nat.le_of_lt n.isLt) i hi).symm)]

/-- The round-t iterate reconstructed from the final transcript agrees with
the iterate before any reply in round t has been queried. -/
theorem upperIterate_prefix_eq_final {d T : ℕ} (P : UpperProgramParameters) (hd : 0 < d)
    {Ω : Type*} (F : Space d → Ω → ℝ) (tape : ℕ → Ω) (seed : UpperSeed d T)
    {t : ℕ} (ht : t ≤ T) :
    upperIterate P seed
        ((upperPairedProgram P hd).toAlgorithm.runPrefix F tape seed (2 * d * t)) t =
      upperIterate P seed
        ((upperPairedProgram P hd).toAlgorithm.finalTranscript F tape seed) t := by
  apply upperIterate_past
  intro i hi
  have hle : 2 * d * t ≤ upperReplyCount d T := Nat.mul_le_mul_left (2 * d) ht
  exact ((upperPairedProgram P hd).toAlgorithm.runPrefix_stable F tape seed hle i hi).symm

noncomputable def upperRecordedSecant {d T : ℕ} (P : UpperProgramParameters)
    (h : Transcript (upperReplyCount d T)) (t : Fin T) (i : Fin d) : ℝ :=
  (transcriptValue h (2 * (t.val * d + i.val) + 1) -
    transcriptValue h (2 * (t.val * d + i.val))) / (2 * P.δ)

/-- The program's two recorded scalar replies yield exactly the same-handle
oracle secant used by the analytic probability lemmas. -/
theorem upperRecordedSecant_eq_oracleSecant {d T : ℕ} (P : UpperProgramParameters) (hd : 0 < d)
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω} {L : ℝ}
    (I : SampleInstance d L P.R Ω μ) (tape : ℕ → Ω) (seed : UpperSeed d T)
    (t : Fin T) (i : Fin d) :
    upperRecordedSecant P ((upperPairedProgram P hd).toAlgorithm.finalTranscript I.sample tape seed) t i =
      I.oracleSecant P.ρ P.δ
        (upperIterate P seed ((upperPairedProgram P hd).toAlgorithm.finalTranscript I.sample tape seed) t.val)
        (Task006.HaarRebalancing.column (seed t).1 i) ((seed t).2 i).val (tape (t.val * d + i.val)) := by
  let h := (upperPairedProgram (T := T) P hd).toAlgorithm.finalTranscript I.sample tape seed
  let nPlus := upperSlot t i (⟨1, by norm_num⟩ : Fin 2)
  let nMinus := upperSlot t i (⟨0, by norm_num⟩ : Fin 2)
  have hp := upperProgram_final_reply P hd I.sample tape seed nPlus
  have hm := upperProgram_final_reply P hd I.sample tape seed nMinus
  change h nPlus = I.sample (upperQueryPoint P hd nPlus seed h) (tape (nPlus.val / 2)) at hp
  change h nMinus = I.sample (upperQueryPoint P hd nMinus seed h) (tape (nMinus.val / 2)) at hm
  have hkp : 2 * (t.val * d + i.val) + 1 < upperReplyCount d T := nPlus.isLt
  have hkm : 2 * (t.val * d + i.val) < upperReplyCount d T := nMinus.isLt
  change (transcriptValue h (2 * (t.val * d + i.val) + 1) -
    transcriptValue h (2 * (t.val * d + i.val))) / (2 * P.δ) = _
  simp only [transcriptValue, dif_pos hkp, dif_pos hkm]
  change (h nPlus - h nMinus) / (2 * P.δ) = I.oracleSecant P.ρ P.δ
    (upperIterate P seed h t.val) (Task006.HaarRebalancing.column (seed t).1 i)
    ((seed t).2 i).val (tape (t.val * d + i.val))
  rw [hp, hm]
  simp only [nPlus, nMinus, upperQueryPoint_slot, upperSlot_handle, Fin.val_mk,
    Nat.one_ne_zero, if_false, if_true]
  unfold SampleInstance.oracleSecant
  have hplus : upperIterate P seed h t.val + P.ρ • ((seed t).2 i).val +
      P.δ • Task006.HaarRebalancing.column (seed t).1 i =
    upperIterate P seed h t.val + P.δ • Task006.HaarRebalancing.column (seed t).1 i +
      P.ρ • ((seed t).2 i).val := by abel
  have hminus : upperIterate P seed h t.val + P.ρ • ((seed t).2 i).val +
      (-P.δ) • Task006.HaarRebalancing.column (seed t).1 i =
    upperIterate P seed h t.val - P.δ • Task006.HaarRebalancing.column (seed t).1 i +
      P.ρ • ((seed t).2 i).val := by rw [neg_smul]; abel
  rw [hplus, hminus]

#print axioms OracleAlgorithm.runPrefix_stable
#print axioms upperProgram_final_reply
#print axioms upperIterate_prefix_eq_final
#print axioms upperIterate_seed_past
#print axioms upperRecordedSecant_eq_oracleSecant

end Task006.Full
