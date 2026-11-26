import MatchingBounds1005.OracleFirstExit
import MatchingBounds1005.OracleMeasurability

/-! First exit as a measurable event of the retained finite oracle transcript.
This permits comparison of true and reference transcript laws. -/
noncomputable section
open MeasureTheory

namespace MatchingBounds1005.Model

theorem replyTranscript_prefix {d : ℕ} {Seed : Type} [MeasurableSpace Seed]
    (reply : (t : ℕ) → Seed → (Fin t → Response d) → Response d) (seed : Seed)
    {m n : ℕ} (hmn : m ≤ n) (i : Fin m) :
    replyTranscript reply seed n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ =
      replyTranscript reply seed m i := by
  induction n with
  | zero => have : m = 0 := Nat.eq_zero_of_le_zero hmn; subst m; exact Fin.elim0 i
  | succ n ih =>
    by_cases heq : m = n + 1
    · subst m; rfl
    · have hmn' : m ≤ n := by omega
      have hi : (⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ : Fin (n + 1)) =
          Fin.castSucc (⟨i.val, lt_of_lt_of_le i.isLt hmn'⟩ : Fin n) := rfl
      rw [replyTranscript, hi, Fin.snoc_castSucc]
      exact ih hmn'

def TraceExit {d T : ℕ} {Seed : Type}
    (safe : (t : ℕ) → Seed → (Fin t → Response d) → Prop)
    (outputSafe : Seed → (Fin T → Response d) → Prop) :
    Set (Seed × (Fin T → Response d)) :=
  {z | (∃ j : Fin T, ¬ safe j.val z.1 (fun i => z.2 ⟨i.val, i.isLt.trans j.isLt⟩)) ∨
    ¬ outputSafe z.1 z.2}

theorem firstExit_iff_traceExit {d T : ℕ} {Seed : Type} [MeasurableSpace Seed]
    (reply : (t : ℕ) → Seed → (Fin t → Response d) → Response d)
    (safe : (t : ℕ) → Seed → (Fin t → Response d) → Prop)
    (outputSafe : Seed → (Fin T → Response d) → Prop) (seed : Seed) :
    seed ∈ FirstExit reply safe outputSafe ↔
      (seed, replyTranscript reply seed T) ∈ TraceExit safe outputSafe := by
  have hp (j : Fin T) : (fun i : Fin j.val =>
      replyTranscript reply seed T ⟨i.val, i.isLt.trans j.isLt⟩) =
        replyTranscript reply seed j.val := by
    funext i
    exact replyTranscript_prefix reply seed (Nat.le_of_lt j.isLt) i
  simp only [FirstExit, TraceExit, Set.mem_setOf_eq, hp]
  constructor
  · rintro (⟨j, hj, hb⟩ | hb)
    · exact Or.inl ⟨⟨j, hj⟩, hb⟩
    · exact Or.inr hb
  · rintro (⟨j, hb⟩ | hb)
    · exact Or.inl ⟨j.val, j.isLt, hb⟩
    · exact Or.inr hb

theorem traceExit_measurable {d T : ℕ} {Seed : Type} [MeasurableSpace Seed]
    (safe : (t : ℕ) → Seed → (Fin t → Response d) → Prop)
    (outputSafe : Seed → (Fin T → Response d) → Prop)
    (hsafe : ∀ j, MeasurableSet {z : Seed × (Fin j → Response d) | safe j z.1 z.2})
    (hout : MeasurableSet {z : Seed × (Fin T → Response d) | outputSafe z.1 z.2}) :
    MeasurableSet (TraceExit safe outputSafe) := by
  have heq : TraceExit safe outputSafe =
      (⋃ j : Fin T, {z : Seed × (Fin T → Response d) |
        ¬ safe j.val z.1 (fun i => z.2 ⟨i.val, i.isLt.trans j.isLt⟩)}) ∪
      {z : Seed × (Fin T → Response d) | ¬ outputSafe z.1 z.2} := by
    ext z
    simp [TraceExit]
  rw [heq]
  apply MeasurableSet.union _ hout.compl
  apply MeasurableSet.iUnion
  intro j
  have hp : Measurable (fun z : Seed × (Fin T → Response d) =>
      fun i : Fin j.val => z.2 ⟨i.val, i.isLt.trans j.isLt⟩) := by
    apply measurable_pi_lambda
    intro i
    exact (measurable_pi_apply (⟨i.val, i.isLt.trans j.isLt⟩ : Fin T)).comp measurable_snd
  exact (hsafe j.val).compl.preimage (measurable_fst.prodMk hp)

end MatchingBounds1005.Model
