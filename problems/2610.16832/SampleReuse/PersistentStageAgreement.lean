import SampleReuse.PersistentStageTable

/-! The immutable-table comparison and the restricted stage simulator
agree until the first activation of the target hidden block. -/

open SecondOrder
open scoped Classical
namespace SampleReuse
noncomputable section
variable {d T : ℕ} {Handle S : Type}

theorem persistentStageTable_before_activation (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : Handle → FirstOrderCoefficients d T R) (j : Fin (T + 1)) (start : ℕ)
    (hp : (persistentComparisonRun P Θ A β table start).1 + 1 = j.val ∨
      (persistentComparisonRun P Θ A β table start).1 = j.val) :
    ∀ n, (∀ t, t < n → ¬0 < firstOrderBlockCompletion (Θ j)
      (firstOrderDilation d T β (persistentComparisonQuery P Θ A β table (start + t)).1 j)) →
      persistentStageTableRun P Θ A β table j start (persistentComparisonRun P Θ A β table start).2 n =
        (persistentComparisonRun P Θ A β table (start + n)).2 ∧
      ((persistentComparisonRun P Θ A β table (start + n)).1 + 1 = j.val ∨
        (persistentComparisonRun P Θ A β table (start + n)).1 = j.val) := by
  intro n
  induction n with
  | zero => intro _; exact ⟨rfl, hp⟩
  | succ n ih =>
    intro hn
    have hh := ih (fun t ht => hn t (by omega))
    have ha := hn n (Nat.lt_succ_self n)
    have hk := firstOrderLimitedProgress_stage_agree Θ β
      (persistentComparisonQuery P Θ A β table (start + n)).1 j
      (persistentComparisonRun P Θ A β table (start + n)).1 hh.2 ha
    have hnext := firstOrderComparisonStep_before_target (persistentPointPolicy P) Θ A β (start + n) j
      (table (persistentComparisonQuery P Θ A β table (start + n)).2)
      (persistentComparisonRun P Θ A β table (start + n)).2
      (persistentComparisonRun P Θ A β table (start + n)).1 hh.2 ha
    constructor
    · rw [persistentStageTableRun, hh.1]
      change P.update (start + n) (persistentComparisonRun P Θ A β table (start + n)).2
        (scaledFirstOrderTruncatedReply Θ A β (table (persistentComparisonQuery P Θ A β table (start + n)).2)
          (firstOrderLimitedProgress Θ β (persistentComparisonQuery P Θ A β table (start + n)).1 j.val)
          (persistentComparisonQuery P Θ A β table (start + n)).1) = _
      rw [← hk]
      rfl
    · exact hnext

theorem persistentStageIndex_before_activation (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : Handle → FirstOrderCoefficients d T R) (j : Fin (T + 1)) (start n : ℕ)
    (hp : (persistentComparisonRun P Θ A β table start).1 + 1 = j.val ∨
      (persistentComparisonRun P Θ A β table start).1 = j.val)
    (hn : ∀ t, t ≤ n → ¬0 < firstOrderBlockCompletion (Θ j)
      (firstOrderDilation d T β (persistentComparisonQuery P Θ A β table (start + t)).1 j)) :
    persistentStageIndex P Θ β j start n
      (persistentStageTableRun P Θ A β table j start (persistentComparisonRun P Θ A β table start).2 n) =
        persistentComparisonIndex P Θ A β table (start + n) := by
  have hh := persistentStageTable_before_activation P Θ A β table j start hp n (fun t ht => hn t (by omega))
  rw [hh.1]
  exact (firstOrderLimitedProgress_stage_agree Θ β
    (persistentComparisonQuery P Θ A β table (start + n)).1 j
    (persistentComparisonRun P Θ A β table (start + n)).1 hh.2 (hn n le_rfl)).symm

/-- The first target activation is present in the actual one-array stage
transcript, including when it occurs only at the final output point. -/
theorem persistentStage_activation_transfer (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : Handle → FirstOrderCoefficients d T R) (j : Fin (T + 1)) (start n : ℕ)
    (a₀ : Fin d → SignedCoefficient R)
    (hp : (persistentComparisonRun P Θ A β table start).1 + 1 = j.val ∨
      (persistentComparisonRun P Θ A β table start).1 = j.val)
    (hn : ∀ t, t < n → ¬0 < firstOrderBlockCompletion (Θ j)
      (firstOrderDilation d T β (persistentComparisonQuery P Θ A β table (start + t)).1 j))
    (ha : 0 < firstOrderBlockCompletion (Θ j)
      (firstOrderDilation d T β (persistentComparisonQuery P Θ A β table (start + n)).1 j)) :
    0 < firstOrderBlockCompletion (Θ j)
      (persistentStagePoint P Θ A β table j start (persistentComparisonRun P Θ A β table start).2 n
        (tableHistory
          (persistentStageKey P Θ A β table j start (persistentComparisonRun P Θ A β table start).2)
          () (targetArrayTable table j a₀) n)) := by
  unfold persistentStagePoint
  rw [persistentStageState_table_history P Θ Θ A β table table j start _ a₀
    (fun _ _ => rfl) (fun _ _ _ => rfl),
    (persistentStageTable_before_activation P Θ A β table j start hp n hn).1]
  exact ha

end
end SampleReuse
