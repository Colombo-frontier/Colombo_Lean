import SampleReuse.PersistentFastTransfer

/-! Completing a positive stage with fewer than its quota forces a marked
activation in the concrete persistent target-table experiment. -/

open SecondOrder
open scoped Classical
namespace SampleReuse
noncomputable section
variable {d T : ℕ} {Handle S : Type}

theorem persistent_reached_fast_marked (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ Θ' : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (past table : Handle → FirstOrderCoefficients d T R) (j : Fin (T + 1)) (start N cap : ℕ)
    (a₀ : Fin d → SignedCoefficient R)
    (hΘ : ∀ i, i.val < j.val → Θ i = Θ' i)
    (hz : ∀ r i, i.val < j.val → past r i = table r i)
    (he : persistentStageEntry P Θ' A β table j.val start)
    (hr : firstOrderStageReached (persistentPointPolicy P) Θ' A β
      (persistentComparisonTape P Θ' A β table) j N)
    (hcount : persistentStageResponseCount P Θ' A β table j.val N < cap) :
    let s₀ := (persistentComparisonRun P Θ' A β table start).2
    let query := persistentStageKey P Θ A β past j start s₀
    let points := persistentStagePoint P Θ A β past j start s₀
    tableHistory (liftPublicQuery query) (Θ' j, ()) (targetArrayTable table j a₀) N ∈
      signTableFastSet query (fun r => r.isSome = true) cap points N := by
  obtain ⟨q, hq, heq⟩ := hr
  have hseq := (persistentStageEntry_as_tape P Θ' A β table (j.val + 1) q).mpr heq
  have hstartq : start ≤ q := by
    by_contra hn
    have hh := persistentStageEntry_no_previous P Θ' A β table he q (by omega)
    rw [hseq.2] at hh
    omega
  have ha := firstOrderStageEntry_target_active (persistentPointPolicy P) Θ' A β
    (persistentComparisonTape P Θ' A β table) j q heq
  have hquery : firstOrderComparisonQuery (persistentPointPolicy P) Θ' A β
      (persistentComparisonTape P Θ' A β table) q = (persistentComparisonQuery P Θ' A β table q).1 := by
    unfold firstOrderComparisonQuery persistentComparisonQuery persistentPointPolicy
    rw [persistentComparisonRun_as_tape]
    rfl
  rw [hquery] at ha
  let active := fun t => 0 < firstOrderBlockCompletion (Θ' j)
    (firstOrderDilation d T β (persistentComparisonQuery P Θ' A β table (start + t)).1 j)
  have hex : ∃ t, active t := by
    refine ⟨q - start, ?_⟩
    change 0 < firstOrderBlockCompletion (Θ' j)
      (firstOrderDilation d T β (persistentComparisonQuery P Θ' A β table (start + (q - start))).1 j)
    rw [Nat.add_sub_of_le hstartq]
    exact ha
  have ht : Nat.find hex ≤ q - start := Nat.find_min' hex (by
    change 0 < firstOrderBlockCompletion (Θ' j)
      (firstOrderDilation d T β (persistentComparisonQuery P Θ' A β table (start + (q - start))).1 j)
    rw [Nat.add_sub_of_le hstartq]
    exact ha)
  exact persistent_original_fast_marked P Θ Θ' A β past table j start (Nat.find hex) N cap a₀ hΘ hz
    (Or.inl (persistentStageEntry_progress P Θ' A β table he)) (by omega)
    (fun t ht => Nat.find_min hex ht) (Nat.find_spec hex) hcount

end
end SampleReuse
