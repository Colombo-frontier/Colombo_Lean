import Bilevel.CappedExecution

/-! Actual displacement-triggered anchor refreshes from the chi refinement.
The count bound holds for every path; no accuracy event is used.
-/
noncomputable section
open scoped BigOperators
namespace Bilevel.CachedAnchorCount

variable {E : Type*} [NormedAddCommGroup E]

structure AnchorState (E : Type*) where
  point : E
  refreshes : ℕ

def track (radius : ℝ) (x : ℕ → E) : ℕ → AnchorState E
  | 0 => ⟨x 0, 0⟩
  | n+1 => if radius < ‖x (n+1) - (track radius x n).point‖ then
      ⟨x (n+1), (track radius x n).refreshes + 1⟩ else track radius x n

/-- The current point is always within the refresh ball after processing. -/
theorem current_within_radius {radius : ℝ} (hr : 0 ≤ radius) (x : ℕ → E) (n : ℕ) :
    ‖x n - (track radius x n).point‖ ≤ radius := by
  cases n with
  | zero => simpa [track] using hr
  | succ n =>
    unfold track
    split
    · simpa using hr
    · exact le_of_not_gt (by assumption)

/-- Remaining displacement is retained as a potential. This prevents paying
for an anchor before its preceding path segment has accumulated enough length. -/
theorem refresh_energy (radius : ℝ) (x : ℕ → E) (n : ℕ) :
    (track radius x n).refreshes * radius + ‖x n - (track radius x n).point‖ ≤
      ∑ i ∈ Finset.range n, ‖x (i+1)-x i‖ := by
  induction n with
  | zero => simp [track]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have ht := norm_sub_le_norm_sub_add_norm_sub (x (n+1)) (x n) (track radius x n).point
    rw [track]
    split
    · rename_i hnew
      simp only [Nat.cast_add, Nat.cast_one, sub_self, norm_zero, add_zero]
      linarith
    · linarith

theorem anchor_count_bound {radius length : ℝ} (hr : 0 < radius)
    (x : ℕ → E) (n : ℕ)
    (hlength : (∑ i ∈ Finset.range n, ‖x (i+1)-x i‖) ≤ length) :
    (1 + (track radius x n).refreshes : ℝ) ≤ 1 + length / radius := by
  have hh := refresh_energy radius x n
  have hcount : ((track radius x n).refreshes : ℝ) * radius ≤ length := by
    linarith [norm_nonneg (x n-(track radius x n).point)]
  exact add_le_add_left ((le_div_iff₀ hr).mpr hcount) 1

theorem refreshes_le_steps (radius : ℝ) (x : ℕ → E) (n : ℕ) :
    (track radius x n).refreshes ≤ n := by
  induction n with
  | zero => simp [track]
  | succ n ih =>
    rw [track]
    split
    · exact Nat.succ_le_succ ih
    · exact ih.trans (Nat.le_succ n)

variable [InnerProductSpace ℝ E]

/-- Apply the actual refresh rule to the actual capped execution. Its number
of anchors is bounded on arbitrary input histories, including failures. -/
theorem all_history_anchor_count {Λ cap radius : ℝ}
    (hΛ : 0 < Λ) (hcap : 0 ≤ cap) (hr : 0 < radius)
    (x₀ : E) (G : ℕ → E) (n : ℕ) :
    let x := fun i => (CappedExecution.run Λ cap x₀ G i).point
    (1 + (track radius x n).refreshes : ℝ) ≤
      1 + (Real.sqrt (n*cap)/Λ)/radius := by
  dsimp only
  let x := fun i => (CappedExecution.run Λ cap x₀ G i).point
  have hb := CachedPathCap.path_length_sq_bound (cap := cap) x
    (CappedExecution.executed Λ cap x₀ G) hΛ n
    (fun i _ => CappedExecution.run_point_step Λ cap x₀ G i)
    (by rw [← CappedExecution.run_energy_eq_sum]
        exact (CappedExecution.run_energy_bounds Λ cap x₀ G hcap n).2)
  have hs : (Real.sqrt (n*cap)/Λ)^2 = n*cap/Λ^2 := by
    rw [div_pow, Real.sq_sqrt (by positivity)]
  have hl : (∑ i ∈ Finset.range n, ‖x (i+1)-x i‖) ≤ Real.sqrt (n*cap)/Λ :=
    (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (by positivity)).mp
      (by rwa [hs])
  exact anchor_count_bound hr x n hl

end Bilevel.CachedAnchorCount
