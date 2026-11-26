import SampleReuse.PersistentStageCounts
import SampleReuse.PersistentLiftedHistory
import SampleReuse.PersistentSignTableBound

/-! An actual original comparison activation with too few stage responses
belongs to the marked fast event of the once-sampled target-array table. -/

open SecondOrder
open scoped Classical
namespace SampleReuse
noncomputable section
variable {d T : ℕ} {Handle S : Type}

theorem persistent_original_fast_marked (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ Θ' : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (past table : Handle → FirstOrderCoefficients d T R) (j : Fin (T + 1)) (start n N cap : ℕ)
    (a₀ : Fin d → SignedCoefficient R)
    (hΘ : ∀ i, i.val < j.val → Θ i = Θ' i)
    (hz : ∀ r i, i.val < j.val → past r i = table r i)
    (hp : (persistentComparisonRun P Θ' A β table start).1 + 1 = j.val ∨
      (persistentComparisonRun P Θ' A β table start).1 = j.val)
    (hnN : start + n ≤ N)
    (hn : ∀ t, t < n → ¬0 < firstOrderBlockCompletion (Θ' j)
      (firstOrderDilation d T β (persistentComparisonQuery P Θ' A β table (start + t)).1 j))
    (ha : 0 < firstOrderBlockCompletion (Θ' j)
      (firstOrderDilation d T β (persistentComparisonQuery P Θ' A β table (start + n)).1 j))
    (hcount : persistentStageResponseCount P Θ' A β table j.val N < cap) :
    let s₀ := (persistentComparisonRun P Θ' A β table start).2
    let query := persistentStageKey P Θ A β past j start s₀
    let points := persistentStagePoint P Θ A β past j start s₀
    tableHistory (liftPublicQuery query) (Θ' j, ()) (targetArrayTable table j a₀) N ∈
      signTableFastSet query (fun r => r.isSome = true) cap points N := by
  dsimp only
  let s₀ := (persistentComparisonRun P Θ' A β table start).2
  let query := persistentStageKey P Θ A β past j start s₀
  let points := persistentStagePoint P Θ A β past j start s₀
  let z := targetArrayTable table j a₀
  have hpoint (u : ℕ) (hu : u ≤ n) : points u (tableHistory query () z u) =
      firstOrderDilation d T β (persistentComparisonQuery P Θ' A β table (start + u)).1 j := by
    change firstOrderDilation d T β (P.query (start + u)
      (persistentStageState P Θ A β past j start s₀ u (tableHistory query () z u))).1 j = _
    rw [persistentStageState_table_history P Θ Θ' A β past table j start s₀ a₀ hΘ hz,
      (persistentStageTable_before_activation P Θ' A β table j start hp u (fun t ht => hn t (by omega))).1]
    rfl
  have hcharge (u : ℕ) (hu : u ≤ n) :
      kernelChargeCount (stageSelected (targetDisclosure query (fun r => r.isSome = true))) cap u
        (tableHistory (liftPublicQuery query) (Θ' j, ()) z u) < cap := by
    have hc := lifted_table_charge_le query (fun r => r.isSome = true) (Θ' j) () z cap u
    rw [persistentStage_response_count P Θ Θ' A β past table j start s₀ a₀ hΘ hz] at hc
    have hb := stageTableCount_le_original P Θ' A β table j start hp u (fun t ht => hn t (by omega))
    have hm := persistentStageResponseCount_mono P Θ' A β table j.val (show start + u ≤ N by omega)
    exact ((hc.trans hb).trans hm).trans_lt hcount
  change tableHistory (liftPublicQuery query) (Θ' j, ()) z N ∈
    kernelStoppedHitSet
      (quotaSafe (stageSelected (targetDisclosure query (fun r => r.isSome = true))) cap
        (kernelHiddenEvent (signStageActivation points)))
      (quotaHit (stageSelected (targetDisclosure query (fun r => r.isSome = true))) cap
        (kernelHiddenEvent (signStageActivation points))) N
  apply tableHistory_stopped_hit _ _ _ _ _ N n (by omega)
  · intro u hu
    refine ⟨hcharge u (by omega), ?_⟩
    change ¬0 < firstOrderBlockCompletion
      (finiteHistoryInitial u (tableHistory (liftPublicQuery query) (Θ' j, ()) z u)).1
      (points u (finiteHistoryMapInitial Prod.snd u (tableHistory (liftPublicQuery query) (Θ' j, ()) z u)))
    rw [tableHistory_initial, tableHistory_liftPublic, hpoint u (by omega)]
    exact hn u hu
  · refine ⟨hcharge n le_rfl, ?_⟩
    change 0 < firstOrderBlockCompletion
      (finiteHistoryInitial n (tableHistory (liftPublicQuery query) (Θ' j, ()) z n)).1
      (points n (finiteHistoryMapInitial Prod.snd n (tableHistory (liftPublicQuery query) (Θ' j, ()) z n)))
    rw [tableHistory_initial, tableHistory_liftPublic, hpoint n le_rfl]
    exact ha

end
end SampleReuse
