import SampleReuse.PersistentEntryFastProbability
import SecondOrder.CurvatureEntrySum

/-! Entrance events are disjoint under the original immutable-table law.
Their multiplicative bounds therefore give one constant per stage, with
no factor proportional to the number of possible entrance times. -/

open SecondOrder
open scoped Classical BigOperators
namespace SampleReuse
noncomputable section
variable {d T : ℕ} {Handle S : Type} [Fintype Handle]

omit [Fintype Handle] in
theorem persistentFastOutcome_entry (P : PersistentFirstOrderPolicy d T Handle S)
    (A β : ℝ) {R : ℝ} (j : Fin (T + 1)) (hj : 0 < j.val) (cap N : ℕ)
    (w : Fin (T + 1) → PersistentBlock d Handle R)
    (hf : persistentFastOutcome P A β j cap N w) :
    ∃ n : Fin (N + 1), persistentEntrySlice P A β j n.val (fun _ _ => True) w := by
  obtain ⟨q, hq, heq⟩ := hf.1
  have hp := persistentStageEntry_progress P (persistentSourceHidden w) A β (persistentSourceTable w)
    ((persistentStageEntry_as_tape P (persistentSourceHidden w) A β (persistentSourceTable w) (j.val + 1) q).mpr heq)
  obtain ⟨n, hn, hen⟩ := persistentStageEntry_exists_before P (persistentSourceHidden w) A β
    (persistentSourceTable w) j.val hj q (by omega)
  exact ⟨⟨n, by omega⟩, hen, trivial⟩

theorem persistent_stage_fast_probability (P : PersistentFirstOrderPolicy d T Handle S)
    (A β R : ℝ) (hR : 2 ≤ R) (j : Fin (T + 1)) (hj : 0 < j.val)
    (N cap : ℕ) (a₀ : Fin d → SignedCoefficient R)
    {L : ℝ} (hL : 0 < L)
    (hlog : L ≤ Real.log (1 / ((N + 1 : ℕ) * (2 * Real.exp (-(d : ℝ) / 128)))))
    (hbudget : 32 * ((cap : ℝ) * ((d : ℝ) / R ^ 2) + Real.log 2) ≤ L) :
    pmfEventProbability (persistentSourceLaw d T Handle R hR)
      (fun w => decide (persistentFastOutcome P A β j cap N w)) ≤ 1 / 32 := by
  let law := persistentSourceLaw d T Handle R hR
  let entry := fun (n : Fin (N + 1)) (w : Fin (T + 1) → PersistentBlock d Handle R) =>
    persistentEntrySlice P A β j n.val (fun _ _ => True) w
  let fast := persistentFastOutcome P A β (R := R) j cap N
  have hu := pmfEventProbability_union law (fun n : Fin (N + 1) => fun w => decide (entry n w ∧ fast w))
  simp only [decide_eq_true_eq] at hu
  have heq : (fun w => decide (∃ n : Fin (N + 1), entry n w ∧ fast w)) =
      (fun w => decide (fast w)) := by
    funext w
    congr 1
    apply propext
    constructor
    · rintro ⟨n, _, hf⟩
      exact hf
    · intro hf
      obtain ⟨n, hn⟩ := persistentFastOutcome_entry P A β j hj cap N w hf
      exact ⟨n, hn, hf⟩
  rw [heq] at hu
  have htime (n : Fin (N + 1)) : pmfEventProbability law (fun w => decide (entry n w ∧ fast w)) ≤
      (1 / 32) * pmfEventProbability law (fun w => decide (entry n w)) :=
    persistent_entry_fast_probability P A β R hR j n.val N cap a₀ hL hlog hbudget
  have hs := Finset.sum_le_sum (fun n (_ : n ∈ Finset.univ) => htime n)
  have ht := hu.trans hs
  rw [← Finset.mul_sum] at ht
  have hd := pmfEventProbability_disjoint_sum_le_one law entry (by
    intro n k w hn hk
    exact Fin.ext (persistentStageEntry_unique P (persistentSourceHidden w) A β (persistentSourceTable w) hn.1 hk.1))
  change pmfEventProbability law (fun w => decide (fast w)) ≤ 1 / 32
  linarith only [ht, hd]

end
end SampleReuse
