import Mathlib.Tactic

/-! # Deterministic part of shadow-oracle accounting

This does not construct or prove a coupling. It verifies the query accounting
once charges to distinct rooms and the per-room threshold have been supplied.
-/

open scoped BigOperators
namespace NCBall

theorem completed_rooms_cost {M N q₀ : ℕ} (charges : Fin M → ℕ)
    (hbudget : ∑ j, charges j ≤ N) (hcomplete : ∀ j, q₀ ≤ charges j) :
    M * q₀ ≤ N := by
  calc
    M * q₀ = ∑ _j : Fin M, q₀ := by simp
    _ ≤ ∑ j, charges j := Finset.sum_le_sum fun j _ => hcomplete j
    _ ≤ N := hbudget

theorem exists_unresolved_room {M N q₀ : ℕ} (charges : Fin M → ℕ)
    (hbudget : ∑ j, charges j ≤ N) (hsmall : N < M * q₀) :
    ∃ j, charges j < q₀ := by
  by_contra h
  push_neg at h
  exact (not_le_of_gt hsmall) (completed_rooms_cost charges hbudget h)

/-- Every scalar evaluation is assigned to at most one room. -/
theorem assigned_query_budget {M N : ℕ} (assignment : Fin N → Option (Fin M)) :
    ∑ j : Fin M, (Finset.univ.filter (fun t => assignment t = some j)).card ≤ N := by
  classical
  have hcount : ∀ t : Fin N,
      (Finset.univ.filter (fun j : Fin M => assignment t = some j)).card ≤ 1 := by
    intro t
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact Option.some.inj ((Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp hb).2)
  calc
    _ = ∑ t : Fin N, (Finset.univ.filter (fun j : Fin M => assignment t = some j)).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    _ ≤ ∑ _t : Fin N, 1 := Finset.sum_le_sum fun t _ => hcount t
    _ = N := by simp

end NCBall
